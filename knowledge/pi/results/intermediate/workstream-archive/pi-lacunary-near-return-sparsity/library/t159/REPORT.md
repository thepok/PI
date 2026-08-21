# T159: marked Palm--Stein audit for overlapping block collisions

Audit date: 2026-08-12 UTC.

Source statements explicitly attributed to Chen--Xia are `literature-checked`
against the pinned primary PDF and exact locators in `SOURCE_PINS.md`. All new
process calculations, probability ranks, asymptotics, and source substitutions
are `proof sketch`. Output of `verify_t159.py` is `finite-test`; it can falsify
the formulas on bounded instances but is not a proof of their universal form.
The fixed-pi premise in Section 10 is separately labeled `unproved pi-transfer`.

```text
PRIMARY_SOURCE_COUNT: 1
PRIMARY_SOURCE_CAP: 6
SCOPED_VERDICT_COUNT: 1
SUCCESSOR_COUNT: 0
FIXED_PI_CLAIM: none
A1_CLAIM: none
C1_CLAIM: none
C2_CLAIM: none
```

## 1. Scope, normalized statement, and ambiguities

The byte-exact `canonical_statement.txt` has SHA-256

```text
cbf56699b651aeb69301265763e38da44feb59c6fd955d2280887e8c06c6a2f8.
```

The canonical question concerns ordered, diagonal-inclusive strict metric near
returns of the fixed orbit `{10^j*pi}`. This note does not change or answer it.
It studies the A10/A13/A14 sibling of exact block equality in an iid decimal
word. Equality is weaker than metric near return; a random-word law does not
control the prescribed digits of pi; and a finite test proves no asymptotic.

Quantifiers and conventions fixed before the audit are:

1. `N>=2` is the number of starts and `m>=1` is the block length.
2. The iid word has exactly `L=N+m-1` independent uniform decimal digits.
3. All blocks are nonwrapping and unpadded.
4. The primitive rare events use unordered off-diagonal pairs, avoiding the
   perfect duplication between `(i,j)` and `(j,i)`.
5. The ordered statistic is reconstructed exactly, with all deterministic
   diagonal pairs restored.
6. The scale audit is `m<=floor((1/4)*log_10 N)`; when nonempty it has
   `N>=10^4`.

## 2. Exact process, endpoints, classes, and marks

Let `D={0,...,9}` and let

```text
X=(X_0,...,X_(L-1)),                 L=N+m-1,
W_i=(X_i,...,X_(i+m-1)),             0<=i<N.
```

The first and last coordinates of `W_i` are `i` and `i+m-1`. The largest last
coordinate is

```text
(N-1)+(m-1)=N+m-2=L-1,
```

so every endpoint is inside the supplied word.

Let

```text
Alpha={{i,j}:0<=i<j<N},              P=#Alpha=binom(N,2),
I_{i,j}=1[W_i=W_j],                  d(i,j)=j-i.
```

The lag mark is the positive integer `d`. Its overlap length and class are

```text
o(i,j)=max(0,m-d),
class(i,j)=OV_o if 1<=d<m, and DISJ if d>=m.
```

The exact digit support and its size are

```text
S_{i,j}=[i,i+m-1] union [j,j+m-1],
#S_{i,j}=m+min(m,d).
```

For `d>=m`, `[i,j+m-1]` is only a hull: its middle gap is not in the support.
Use the deterministic unique mark

```text
u_{i,j}=(i,j,d,class(i,j))
```

in the finite discrete carrier space, and define the simple marked process

```text
Xi=sum_{{i,j} in Alpha} I_{i,j} delta_{u_{i,j}},
Z=|Xi|=sum_Alpha I_{i,j}.
```

Deterministic marks are independent random elements, so they meet the source's
mark-independence condition. The exact ordered, diagonal-inclusive collision
process and count are reconstructed, not approximated, by

```text
Xi_ord=sum_(i=0)^(N-1) delta_(i,i,0,DIAG)
       +sum_(i<j) I_{i,j}[delta_(i,j,d,class)+delta_(j,i,-d,class)],
E=|Xi_ord|=N+2Z.                                           (2.1)
```

The diagonals are deterministic and reversal gives the same event twice;
putting either into the primitive Bernoulli family would destroy a Poisson
rare-event interpretation.

## 3. Exact one- and two-event probabilities

For one pair at lag `d`, the equations `X_(i+r)=X_(j+r)`, `0<=r<m`, form an
equality graph on `m+min(m,d)` vertices. It has `min(m,d)` connected components,
and therefore rank exactly `m`. Thus, including the overlapping case,

```text
p=P(I_{i,j}=1)=10^(-m),
lambda=E[Z]=P*p=binom(N,2)*10^(-m),
lambda_d=(N-d)*10^(-m).                                  (3.1)
```

This rules out the tempting but false probability `10^(-(m-d))` for `d<m`.
For two indices `alpha,beta`, let `G_{alpha,beta}` be the union of their
equality edges. If it has `v` vertices and `c` connected components, then

```text
P(I_alpha I_beta=1)=10^(-(v-c)).                          (3.2)
```

Distinct events have rank at least `m+1`, hence

```text
P(I_alpha I_beta=1)<=10^(-(m+1))=p/10.                   (3.3)
```

Equality in (3.3) occurs, for example, for lags one and two placed at the same
start. Shared support alone need not create covariance; only duplicated edges
or cycles lower the union rank.

For same-lag translates

```text
alpha={i,i+d}, beta={i+h,i+h+d}, h!=0,
```

the union is acyclic and has `(m-|h|)_+` duplicated edges. Therefore

```text
P(I_alpha I_beta=1)=10^(-m-min(m,|h|)).                  (3.4)
```

## 4. Dependency neighborhoods

For a start `t`, put

```text
H_t={s in {0,...,N-1}:|s-t|<=m-1}.
```

These are exactly the block starts whose digit intervals meet `W_t`. For
`alpha={i,j}`, define

```text
U_alpha=H_i union H_j,
A_alpha={beta={k,l} in Alpha:{k,l} intersects U_alpha}.
```

This includes `alpha`. If `beta` is outside `A_alpha`, its digit support is
disjoint from `S_alpha`. More strongly, `I_alpha` is independent of the entire
sigma-field generated by all such outside indicators, because that sigma-field
uses only outside digits. This is the local-dependence condition and makes the
source's `epsilon_1` exactly zero.

Writing `R_alpha=#U_alpha`, direct complementary counting gives

```text
#A_alpha=binom(N,2)-binom(N-R_alpha,2)
        =R_alpha*(2*N-R_alpha-1)/2.                       (4.1)
```

Boundary truncation can only decrease `R_alpha`, and

```text
R_alpha<=R_*=min(N,4*m-2),
#A_alpha<=D_*=R_*(2*N-R_*-1)/2.                          (4.2)
```

The endpoint `m`, rather than `m+1`, is correct: blocks whose starts differ by
exactly `m` are disjoint.

## 5. One-source marked Palm--Stein substitution

**Source theorem (`literature-checked`).** Chen--Xia Theorem 4.1, printed
pp. 2555--2556 (PDF pp. 11--12), treats
`M=sum_i I_i delta_{U_i}` with independent marks, arbitrary neighborhoods
`A_i` containing `i`, outside count `V_i=sum_(j notin A_i)I_j`, and Poisson
mean measure `sum_i p_i Law(U_i)`. Its exact `d2` bound has:

```text
sum_i sum_(j in A_i\{i}) (5/lambda+3/(V_i+1)) E[I_i I_j]
+ min(epsilon_1,epsilon_2)
+ sum_i sum_(j in A_i)
    (5/lambda+E[3/(V_i+1)|I_j=1]) p_i p_j.                (5.1)
```

Here `d2` is the bounded second Wasserstein pseudometric defined on printed
p. 2552 (PDF p. 8), not quadratic optimal-transport `W_2`. Remark 4.2 says the
bound does not depend on the mark laws when the Poisson mean reflects them.
Remark 4.3 lifts nonsimple marked processes to make neighborhoods explicit.
Exact source notation, both epsilon terms, and Palm coupling requirements are
recorded in `SOURCE_PINS.md`.

Substitute Sections 2--4 into (5.1). Use `epsilon_1=0`, (3.3),
`1/(V_alpha+1)<=1`, its conditional version `<=1`, and (4.2). Every step is
explicit, giving

```text
d2(Law(Xi),Po(lambda_mark))
 <= (5/lambda+3)*P*[(D_*-1)*p/10+D_*p^2]
 =: B_CX(N,m).                                             (CX-159)
```

This is a valid conservative source-theorem substitution, not a sharp claim.
It does not import the T155 note's valid independent-alphabet toy substitution:
for the raw overlapping-word process audited here, joint probability can be
`p/10`, not always `p^2`.

At the prescribed scale, `p>=N^(-1/4)` and
`lambda>=binom(N,2)N^(-1/4)`. Nevertheless `(CX-159)` is noninformative:
already its displayed first summand is of order `P*D_*p`, while the target
metric is bounded by one. Thus this explicit Chen--Xia substitution does not
certify convergence to a simple Poisson location process. This conclusion is
only about `(CX-159)`, not a lower bound on every possible approximation.

## 6. Mean versus overlap-cluster scale

The ordered expected collision count is

```text
E[E]=N+2*lambda=N+N*(N-1)*10^(-m).                        (6.1)
```

For a T7 sibling calibration with parameter `A`, its mean is below the screen
`N^2/(A*m)` exactly when

```text
A*m*[1/N+(1-1/N)*10^(-m)]<=1.                            (6.2)
```

Define the directed same-lag translated excess-joint mass

```text
Delta_parallel
 =2*sum_(h=1)^(min(m-1,N-2)) binom(N-h,2)
       *[10^(-m-h)-10^(-2m)].                             (6.3)
```

The factor two orients the pair `(alpha,beta)`; it is not reversal of a block
collision. Formula (3.4) proves (6.3). For `N/m -> infinity`,

```text
Delta_parallel/lambda
 ->2*sum_(h=1)^(m-1)(10^(-h)-10^(-m)),
```

and then as `m->infinity` this tends to `2/9`. Equivalently, it tends to `1/9`
of the ordered off-diagonal mean `2*lambda`. Thus this explicit overlap-cluster
factorial-cumulant contribution does **not** separate as `o(mean)`. This is a
moment-budget obstruction to discarding clusters, not a proved lower bound on
`d2` or a proof that every simple-Poisson approximation fails.

At the coarser T7 threshold `T=N^2/(A*m)`, however,

```text
Delta_parallel/T ~ A*m*10^(-m)/9.                        (6.4)
```

For fixed `A` this tends to zero with `m`. Thus the answer to the audit question
has two parts: mean and cluster are inseparable at relative Poisson scale, but
both can be separated from the much larger T7 threshold whenever (6.2) has
slack. This random-model fact supplies no fixed-word membership statement.

## 7. Five separator tests

Each test uses the fixed definitions above. Universal calculations are
`proof sketch`; bounded replay instances are `finite-test`.

1. **Constant word.** All `N` blocks agree, so `Z=binom(N,2)` and `E=N^2`.
   This maximally violates a nontrivial T7 screen and shows why deterministic
   diagonals and event multiplicity cannot be hidden in the Poisson mean.
2. **Periodic word.** For a primitive period-`r` word, `m>=r`, and `N` a
   multiple of `r`, exactly `r` block types each occur `N/r` times. Hence
   `E=N^2/r` and `Z=(N^2/r-N)/2`. Local event structure alone does not bound
   this global phase multiplicity.
3. **Repeated de Bruijn word.** Repeat a cyclic decimal de Bruijn word of order
   `m`, take `N` divisible by `10^m`, and append the required look-ahead. Every
   length-`m` block occurs `N/10^m` times, so `E=N^2/10^m` and
   `Z=(N^2/10^m-N)/2`, exactly the iid off-diagonal scale up to the factor
   `1-1/N`.
4. **Shared prefix.** If coordinates `0,...,R+m-2` are fixed equal, the first
   `R` blocks agree. Thus `Z>=binom(R,2)` and `E>=R^2`. Taking
   `R=ceil(N/sqrt(m))` reaches the T7 threshold scale without contradicting an
   iid law, because the family itself has exponentially small probability.
5. **Iid conditioned on one long repeat.** Condition on
   `C={W_0=W_1}`. This is a length-`m` repeat at lag one and has probability
   `10^(-m)`. For every `beta`, (3.2) gives the exact conditional probability
   `P(I_beta=1|C)=10^(-(rank(G_{C,beta})-m))`; consequently
   ```text
   E[Z|C]=sum_(beta in Alpha)10^(-(rank(G_{C,beta})-m)).   (7.1)
   ```
   The conditioning forces `X_0=...=X_m`, hence at least the event `C`, and it
   raises nearby same-lag probabilities according to (3.4). The replay checks
   (7.1) by exact enumeration for `N=5,m=2` and by graph ranks for `N=8,m=3`.

## 8. Comparison with T150, T152, T154--T158

Exact report hashes and availability evidence are in `COMPARATORS.md`. No
comparator deduction is imported as a theorem.

| item | supplied level and fingerprint | T159 boundary |
|---|---|---|
| T150 | source claims `literature-checked`; deductions `proof sketch`; finite replay `experiment`; reuse-adjusted separately-Lipschitz Gibbs bad-word census | T159 counts marked collision locations under iid digits; it uses no Gibbs concentration or all-word census. |
| T152 | unverified `proof sketch` note plus finite `experiment`; maximal-depth exact-type fractional-cover entropy census | T159 uses neither Shannon entropy, type strata, nor fractional covers. |
| T154 | unverified `proof sketch` note plus finite `experiment`; interval-packing/coordinate-price entropy LP and asserted matching reuse rate | T159 uses no entropy LP or duality and does not treat the note's headline as verified. |
| T155 | pinned source lead; retained F1 marked Palm--Stein model, with deductions only `proof sketch` | T159 intentionally specializes the same fingerprint. Its delta is exact overlap supports/ranks, ordered reconstruction, corrected joint probabilities, and the five tests; no novelty claim is made. |
| T156 | no readable artifact in the refreshed snapshot; metadata says a pinned delivery received `revise` for two source-locator defects | Identifier reserved. No semantic distinction or nonduplication claim is possible. |
| T157 | source claims `literature-checked`; deductions `proof sketch`; finite replay `experiment`; inverse Littlewood--Offord GAP/LCD/Halasz screens for block-difference vectors | T159 is a forward local-dependence process approximation and uses no inverse concentration or coefficient vectors. |
| T158 | active generation-1 lease only; no readable agenda, report, source, theorem, hash, or verification level | Identifier reserved. No semantic distinction or nonduplication claim is possible. |

## 9. What failed and what remains useful

The one-source audit is sufficient: Chen--Xia already contains the marked
Bernoulli process theorem, exact constants, outside-dependence term, and lifting
device. More sources would not repair the model's explicit same-lag clusters.
The failure is localized rather than generic: the support neighborhood has
`Theta(mN)` potential neighbors per event, the conservative source substitution
is vacuous, and the exact translated cluster excess remains a constant fraction
of the mean. The lag-marked mean measure and rank formulas remain a checkable
random-model benchmark.

## 10. Separate unproved pi-specific premise

**PI-PALM-DEPENDENCE-T159 (`conjecture`; `unproved pi-transfer`; NOT
ASSERTED).** On an increasing sequence of prefixes of the actual decimal orbit
of pi, there exists a proved probabilistic or deterministic surrogate whose
ordered diagonal-inclusive collision locations have the exact endpoint
conversion (2.1), whose lag-marked mean satisfies a T7-scale inequality, whose
non-Poisson overlap clusters are explicitly controlled, and whose exceptional
set is proved not to contain the prescribed pi word.

No inspected source supplies this premise. An iid distributional statement
cannot exclude one fixed word, and exact block equality remains weaker than the
canonical metric event. No fixed-pi, A1, C1, or C2 conclusion is claimed.

## 11. Replay and verdict

From a directory containing only the delivered artifacts, run

```bash
python3 verify_t159.py > replay.txt
diff -u raw_output.txt replay.txt
sha256sum -c SHA256SUMS
```

The replay checks source and canonical hashes, theorem anchors, source cap,
all endpoint/support/neighborhood identities on bounded ranges, equality-graph
probabilities, both displayed error formulas, all five separator tests,
comparator markers, label firewalls, and endpoint counts.

SCOPED_VERDICT (1/1): **hold as model**.

Hold only the lag-marked iid benchmark and its mean-versus-cluster diagnostic.
Do not develop this simple-Poisson transfer: `(CX-159)` is noninformative in the
mandated regime and the exact same-lag factorial-cumulant contribution is not
`o(mean)`. This verdict does not prove a metric lower bound, and it does not
close sharper simple-Poisson bounds, compound-Poisson approximations generally,
G28, or any fixed-pi route.

SUCCESSOR (0/1): **none**.
