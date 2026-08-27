# T67: short-lag decimal components do not aggregate from individual window bounds

Status: `proof sketch` for the new finite-word and component arguments below;
the imported T36 and T56 theorem statements identified in Section 2 are
`machine-checked`. Verdict: **INSUFFICIENT**. This note makes no unconditional
claim about pi, C7, C2, C1, or positive decimal factor entropy.

## 1. Provenance, normalized question, and ambiguities

The canonical source is the locally formulated file
`pi-positive-decimal-factor-entropy.txt`; no original source URL was recorded.
Its byte-exact SHA-256 is

```text
a70dd741b27595aeb3dfc902b5e201579fed6bae24e2191f58c5ac64a22939e6
```

The canonical question asks whether there are fixed `eta>0` and `N>=1` such
that `p_pi(n)>=10^(eta*n)` for every integer `n>=N`. T67 does not answer that
question. It audits a proposed route to the conditional C7 frontier.

For the whole note:

* decimal positions are zero-based;
* `[u,v)` means the integer sites `u,u+1,...,v-1`;
* `n>=1` is the decimal resolution;
* `L_n=10^(floor(n/2))`, exactly T56's natural-number division `10^(n/2)`;
* a positive short lag satisfies `1<=r<n` and `r<L_n`;
* an upper-triangular start satisfies `0<=j<L_n-r`;
* all circle near-return cutoffs are strict;
* T56 restores the reverse orientation by multiplying upper-triangular counts
  by two, and its separate diagonal term is `L_n`.

The phrase "near return gives equal decimal blocks" is ambiguous and, read
literally, false. The endpoint-safe result is equal **or cyclically adjacent**
numeric block labels. Section 3 retains all five alternatives. The phrase
"overlap component has the gcd period" is also false for arbitrary nonempty
overlaps. Section 4 states the required Fine-Wilf overlap threshold.

## 2. Kernel-checked inputs and exact hypotheses

### 2.1 T56 ranges and target

The accepted knowledge-library module, recorded by the workflow as
`machine-checked`,
`TheoryLib.PiPositiveDecimalFactorEntropy.T56T56LagSectorAudit` has source hash

```text
41e8ec69c4a113592b8f1de1dc5e02e815726c5a7e541ac7fd57afc6b181f1cc
```

Its theorem `sparse_Q_exact_lag_decomposition` gives, for `n>=1`,

```text
Q_pi(n,L_n)
 = L_n
   + 2 * sum_(1<=r<=L_n-1)
       |{j: 0<=j<L_n-r,
          rho(10^j*(10^r-1)*pi) < 10^(-n)}|.          (2.1)
```

Here `rho(t)=inf_(z in Z)|t-z|`. The theorem
`mem_sparse_short_sector_iff` makes the short range exactly

```text
0<r,  r<n,  r<L_n.                                   (2.2)
```

Fix real `mu,c` and natural `Q0`. T25/T56 use the explicit premise

```text
EI_c(pi,mu,c,Q0) :<=>
 c>0 and mu>1 and
 for every natural q>=Q0 with q>0 and every integer z,
 c/q^mu < |pi-z/q|.                                  (2.3)
```

For `q(j,r)=10^j*(10^r-1)`, T25's arithmetic exclusion mask is

```text
ArithmeticExcluded(mu,c,Q0,n,j,r) :<=>
 Q0<=q(j,r) and 10^(-n)<=q(j,r)*c/q(j,r)^mu.         (2.4)
```

Equality belongs to the excluded side because (2.1) is strict. The short
residual upper-triangular set is therefore

```text
R_n^+(mu,c,Q0) :=
 {(j,r): 0<r<n, r<L_n, 0<=j<L_n-r,
          rho(q(j,r)*pi)<10^(-n),
          not ArithmeticExcluded(mu,c,Q0,n,j,r)}.   (2.5)
```

By definition,

```text
shortResidualPairCount(mu,c,Q0,n,L_n)=2*|R_n^+|.    (2.6)
```

Under (2.3), `sparse_Q_eq_diagonal_add_short_add_long` gives

```text
Q_pi(n,L_n)=L_n+S_n+Rlong_n,                         (2.7)
```

where `S_n=2*|R_n^+|`. The exact desired short predicate is

```text
exists A>0, exists N>=1, for every n>=N,
S_n<=A*L_n.                                          (2.8)
```

If (2.3), (2.8), and an eventual bound `Rlong_n<=B*L_n` hold, the
kernel-checked theorem `sparse_sector_linear_bounds_imply_QBound` gives
T56/T27's sparse microscopic predicate with constant exactly `1+A+B`.
None of these three premises is asserted for pi here.

### 2.2 T36 periodic-window estimate

The accepted knowledge-library module recorded as `machine-checked` and
containing
`DecimalFactorComplexity.PeriodicWindowGap.effectiveIrrationality_periodic_window_gap`
has source hash

```text
900e9fdeefbaea73236435b3845cd9dcc3c3b07b93d2e244b94dc39f4c109781
```

For a stream `d:N->{0,...,9}`, T36 defines

```text
ExactPeriodicWindow(d,a,p,W) :<=>
 p>0 and for every 0<=i<W, d(a+i)=d(a+(i mod p)).    (2.9)
```

Thus the half-open window is exactly `[a,a+W)`, and `p` need not be the
least period. If `x=Real.ofDigits(d)`, T36's **separate constant-one** premise

```text
EI_1(x,mu,Q0) :<=>
 mu>1 and for every natural q>=Q0 with q>0 and every integer z,
 1/q^mu < |x-z/q|                                   (2.10)
```

and the onset

```text
Q0<=10^a*(10^p-1)                                   (2.11)
```

imply the displayed bound

```text
W <= (mu-1)*a + mu*p + 1.                            (2.12)
```

The final `1` is T36's explicit rounding constant. T67 tests whether the
family of inequalities (2.12), even when imposed on individual and maximal
periodic components, can yield (2.8). It cannot. The counterfamily in Section
6 satisfies (2.12), not the effective irrationality premise (2.10).

## 3. Endpoint-safe translation of T56 near returns

For a decimal stream `d`, define its length-`n` label at `j` by

```text
A_n(j)=sum_(t=0)^(n-1) d(j+t)*10^(n-1-t),
0<=A_n(j)<10^n.                                      (3.1)
```

The canonical half-open cell of label `A` is

```text
C_n(A)=[A/10^n,(A+1)/10^n).                          (3.2)
```

T2's kernel-checked theorem `nearReturn_implies_prefixLabels_adjacent`, with
source hash

```text
1f0a50bc5286e997b897d03d49cc2613370c4cea0a20e41340f099b6278ff174
```

states the endpoint-safe consequence of a strict radius `10^(-n)` return.
Writing `A=A_n(j)`, `B=A_n(j+r)`, and `q=10^n`, it is exactly

```text
B=A
or B+1=A
or A+1=B
or (A=0 and B+1=q)
or (B=0 and A+1=q).                                  (3.3)
```

The last two cases are the circle wrap `0 <-> q-1`. Closed decimal cells are
allowed in the checked theorem; strictness is what excludes a jump across two
cell widths. For pi, T7's kernel-checked
`piNearReturnPairs_subset_three_codeGraphs` packages (3.3) as identity,
cyclic successor, or cyclic predecessor code graphs. Its finite comparison
`piCylinderCollisionEnergy_le_Q_pi_le_three_mul` gives

```text
equal-block energy <= Q_pi <= 3*equal-block energy.  (3.4)
```

This is an aggregate comparison, not a pairwise equality assertion.

The decimal carry in (3.3) is completely explicit. If `A=B+1` without wrap,
let `ell` be the number of trailing nines in the `n`-digit expansion of `B`.
Then `0<=ell<n`, and for a uniquely determined common prefix `u` and digit
`b in {0,...,8}`,

```text
B = u  b    99...9   (ell trailing nines),
A = u (b+1) 00...0   (ell trailing zeros).          (3.5)
```

The case `B=A+1` reverses (3.5). At wrap, the two words are `99...9` and
`00...0`. Therefore a strict near return can have a carry defect of any length
from zero through `n`; it need not provide an exact periodic window.

In the identity branch `A_n(j)=A_n(j+r)`, however, the two blocks agree:

```text
d(j+t)=d(j+r+t) for every 0<=t<n.                    (3.6)
```

Set

```text
J(j,r)=[j,j+n+r).                                    (3.7)
```

Equation (3.6) is equivalent to saying that the word on `J(j,r)` has period
`r`: for offsets `r<=i<n+r`, repeatedly subtract `r` until reaching
`0,...,r-1`; (3.6) supplies every subtraction. Conversely, a period-`r` word
on (3.7) gives (3.6) immediately. Thus the exact T36 parameters contributed
by an equal-label event are

```text
a=j,  p=r,  W=n+r.                                   (3.8)
```

The reverse metric implication is endpoint-safe. Two canonical orbit points
in the same half-open cell (3.2) have ordinary distance strictly below its
width `10^(-n)`, hence circle distance strictly below that width. For pi this
direction is also kernel-checked as
`pi_factor_eq_implies_circleDistance_lt`. There is no checked converse from a
T56 near return to equality; (3.3) is the exact converse substitute.

## 4. Overlap components and the Fine-Wilf threshold

Consider only equal-label events for the moment. Give the event `v=(j,r)` the
periodic interval `J_v=J(j,r)` and period `p_v=r`. Two events overlap when
`J_v intersect J_w` is nonempty. Connected components for this relation have
interval supports because a connected union of integer intervals is an
integer interval. Mere nonempty overlap does **not** force a common gcd
period.

The exact finite Fine-Wilf lemma used here is:

> If a finite word of length `m` has periods `p` and `q`, and
> `m>=p+q-gcd(p,q)`, then it has period `gcd(p,q)`.

One direct proof puts edges of lengths `p` and `q` between valid positions.
Periodicity makes the word constant on graph components. Under the displayed
length bound, the Euclidean-algorithm walk never needs to leave the interval,
so all positions congruent modulo `gcd(p,q)` lie in one component. The bound
is sharp in general. This is the classical Fine-Wilf theorem; the result is
not imported as a premise because the preceding graph proof applies directly.
For attribution: N. J. Fine and H. S. Wilf, "Uniqueness Theorems for Periodic
Functions," *Proceedings of the AMS* 16 (1965), 109-114,
DOI `10.1090/S0002-9939-1965-0174934-9`.

For intervals carrying periods `p` and `q`, define the overlap length

```text
ov([a,b),[c,d))=max(0,min(b,d)-max(a,c)).             (4.1)
```

A **Fine-Wilf merge** is allowed only when

```text
ov >= p+q-gcd(p,q).                                  (4.2)
```

The overlap then has period `g=gcd(p,q)`. Here is the propagation step in
full. Condition (4.2) is at least `p` and at least `q`. Any `p` consecutive
overlap positions represent every residue modulo `p`. Since `g` divides `p`,
the overlap's period-`g` equalities identify all residues modulo `p` that are
congruent modulo `g`. Period-`p` propagation therefore makes the entire first
interval period `g`. The same argument with `q` makes the second interval
period `g`. Their period-`g` phases agree on the nonempty overlap, so their
union is period `g`.

For complete inspectability, a certified component is built recursively.
Start with one event, support `U_1=J_1`, and `g_1=p_1`. After events
`1,...,k-1` have interval support `U_(k-1)` and period

```text
g_(k-1)=gcd(p_1,...,p_(k-1)),                        (4.3)
```

event `k` may be merged only if

```text
ov(U_(k-1),J_k)
 >= g_(k-1)+p_k-gcd(g_(k-1),p_k).                   (4.4)
```

Then

```text
U_k=U_(k-1) union J_k,
g_k=gcd(g_(k-1),p_k).                                (4.5)
```

Induction using the preceding two-period lemma gives: if the final support is
`U=[A,B)`, then its full word is exactly periodic with period

```text
g=gcd{r : (j,r) is in the certified component}.      (4.6)
```

This is the promised explicit gcd/component bound. Under T36's premises
(2.10)-(2.11), applied at `(a,p,W)=(A,g,B-A)`, it becomes

```text
B-A <= (mu-1)*A + mu*g + 1.                          (4.7)
```

Equation (4.7) controls the component **span**. It contains no factor
controlling how many events `(j,r)` lie in that span. Raw overlap components
that fail (4.4) do not even receive (4.7) without an additional argument.

## 5. Why the component estimate does not imply T56

There are two independent losses.

First, T56's actual vertices satisfy (3.3), not necessarily (3.6). Adjacent
labels carry one pivot defect and a possibly length-`n` carry tail. Thus T36
does not apply to every T56 vertex.

Second, grant the stronger assumption that every short near return is in the
identity branch and that every overlap component is Fine-Wilf certified.
T36 then gives only (4.7). A span of `O(n)` can contain `Theta(n^2)` pairs
because there are `n-1` possible short periods and `Theta(n)` starts for each.
Disjoint such spans can fill `[0,L_n)`, producing `Theta(n*L_n)` events.

Consequently T36's individual or component span inequalities alone do not
produce the short estimate (2.8); merely adding an independently supplied
long-sector bound to T56's partition leaves that short premise undisposed.
The following family isolates this short-sector aggregation failure. It does
not satisfy or test a long-sector hypothesis for the same seed.

## 6. Explicit moving-seed counterfamily

Fix an integer `n>=6`, and put `S=4n`. Define the infinite decimal word
`d^(n)` by

```text
d^(n) = 2^n 3^n 4^n 6^n followed by (0^(4n) 5^n) repeated forever.  (6.1)
```

Here `a^m` means `m` repetitions of digit `a`, and the final parenthesized
word repeats forever. Equivalently, after position `S`,

```text
d^(n)(S+5nk+t)=0 for 0<=t<4n,
d^(n)(S+5nk+t)=5 for 4n<=t<5n.                       (6.2)
```

The corresponding moving rational seed is explicitly

```text
x_n = (2/9)(1-10^(-n))
    + (3/9)(10^(-n)-10^(-2n))
    + (4/9)(10^(-2n)-10^(-3n))
    + (6/9)(10^(-3n)-10^(-4n))
    + (5/9)(10^(-8n)-10^(-9n))/(1-10^(-5n)).         (6.3)
```

This expansion is nonterminating and not eventually nine, so its canonical
floor-based decimal digits are exactly (6.1).

### 6.1 Classification and components

All consecutive transitions in (6.1) are separated by at least `n` sites. A
nonconstant period-`r` word of length `n+r`, with `0<r<n`, has two transitions
at distance `r`: translate any transition by `r` into the word, using the
backward translate if the forward one leaves the interval. Therefore no such
periodic word can cross a transition of (6.1).

It follows that an equal-block event (3.6) occurs exactly when `J(j,r)` lies
inside a constant run. Runs of length `n` cannot contain a window of length
`n+r`; hence every event lies in one of the zero runs

```text
P_k=[A_k,A_k+4n),  A_k=4n+5nk,  k>=0.                (6.4)
```

All events inside one `P_k` form one overlap component: lag-one windows at
successive starts overlap and join the whole run. Different `P_k` are
separated by `[A_k+4n,A_k+5n)`, so their half-open supports are disjoint.
Every component has exact least period `1`, span `4n`, and gcd `1`.

### 6.2 Every T36 numerical bound holds

Choose `mu=2`. For every individual event, (3.8) and `j>=4n` give

```text
n+r <= j+2r+1,                                       (6.5)
```

indeed the right side minus the left side is `j+r+1-n>0`. For the maximal
component (6.4), T36's bound is

```text
4n <= A_k+2*1+1,                                     (6.6)
```

which holds already with three units of slack at `k=0`. Thus this family
satisfies both every individual displayed T36 inequality and every maximal
gcd-component inequality.

This does not assert (2.10): `x_n` is rational and cannot satisfy a genuine
effective irrationality lower bound against all rationals. The logical test
here is exactly whether T36's resulting family of numerical window bounds can
be aggregated. It cannot.

### 6.3 Exact T56 ranges, strictness, and residual mask

Let `L_n=10^(floor(n/2))` and

```text
K_n=floor((L_n-4n)/(5n)).                             (6.7)
```

For each `0<=k<K_n`, each `1<=r<n`, select precisely

```text
A_k <= j <= A_k+3n-r.                                (6.8)
```

Then `J(j,r)` lies in `P_k`. Its endpoint is at most `A_k+4n<=L_n`, so
`j<L_n-r`; all selected events satisfy the complete T56 short range.

The two length-`n` blocks are equal and their orbit tails lie in the same
half-open decimal cell, whose diameter is strictly below `10^(-n)`. Therefore

```text
rho(10^j*(10^r-1)*x_n)<10^(-n).                      (6.9)
```

For the moving-seed analogue of T25's mask, choose `mu=2,c=1`, and arbitrary
`Q0`. Since `j>=4n>=n` and `r>=1`,

```text
q(j,r)=10^j*(10^r-1) >= 9*10^n > 10^n.              (6.10)
```

The second conjunction in (2.4) would read `10^(-n)<=1/q(j,r)`, which is
false by (6.10). Hence every selected event is residual, independently of
`Q0`.

### 6.4 Exact multiplicity

At fixed lag `r`, (6.8) has exactly `3n-r+1` starts. One component therefore
has upper-triangular multiplicity

```text
M_n=sum_(r=1)^(n-1)(3n-r+1)
   =(n-1)(5n+2)/2.                                   (6.11)
```

Restoring both orientations, the selected count is exactly

```text
I_n=2*K_n*M_n=K_n*(n-1)*(5n+2).                      (6.12)
```

For `n>=6`, elementary decimal growth gives

```text
4n<=L_n/2,
K_n>=L_n/(20n).                                      (6.13)
```

Indeed `(L_n-4n)/(5n)>=L_n/(10n)>=2`, and the floor of a real number at least
two is at least half that number. Since `n-1>=n/2` and `5n+2>=5n`,

```text
I_n >= (1/8)*n*L_n.                                  (6.14)
```

For every proposed real constant `C>0`, choose an integer `n>=6` with
`n>8C`. Then (6.14) gives `I_n>C*L_n`. This is an explicit moving-seed
counterfamily to any uniform aggregation implication using only the tested
individual and maximal-component T36 bounds.

It is not a counterexample involving one fixed seed, effective irrationality,
or pi. It does not say that (2.8) is false for pi.

## 7. One exact missing cluster-multiplicity premise

Return to the actual residual set (2.5), including all five endpoint-safe
label cases. Give each vertex `v=(j,r)` the support

```text
J_v=[j,j+n+r).                                       (7.1)
```

Join two vertices when their supports intersect, and let `Comp_n` be the
finite set of connected components. For `C in Comp_n`, let

```text
U(C)=union_(v in C) J_v,
len(U(C))=max(U(C))+1-min(U(C)).                      (7.2)
```

Each `U(C)` is an integer interval. Supports of distinct components are
disjoint, and every support lies in `[0,L_n+n)`. The following is one fully
quantified missing premise for fixed `mu,c,Q0`:

```text
ClusterMultiplicity(mu,c,Q0) :<=>
 exists K>0, exists N>=2, for every integer n>=N,
 for every C in Comp_n,
 |C| <= K*len(U(C)).                                  (7.3)
```

No periodicity conclusion is built into (7.3); it applies equally to carry
and wrap vertices. Since the component supports are disjoint,

```text
|R_n^+| = sum_C |C|
         <= K*sum_C len(U(C))
         <= K*(L_n+n)
         <= 2K*L_n                                  (7.4)
```

for `n>=N`, because `n<=L_n` for `n>=2`. By (2.6),

```text
S_n<=4K*L_n.                                         (7.5)
```

Thus (2.3), (7.3), and an eventual long-sector estimate
`Rlong_n<=B*L_n` imply T56's sparse microscopic predicate with explicit
constant

```text
1+4K+B                                               (7.6)
```

and onset the maximum of the three onsets. T56/T27 then conditionally gives
C7 with its already checked conversion constant. No premise in this paragraph
is asserted for pi.

The counterfamily diagnoses (7.3) sharply. One component has support length
`4n` and multiplicity (6.11), hence

```text
M_n/(4n)=(n-1)(5n+2)/(8n),                           (7.7)
```

which grows like `5n/8`.

## 8. Verdict and nonclaims

**INSUFFICIENT.** The exact endpoint-safe translation of T56 near returns is
the five-way adjacent-label statement (3.3), so periodic windows cover only
its identity branch. Within that branch, Fine-Wilf-compatible components have
the gcd period and obey the explicit conditional T36 span estimate (4.7).
The moving family (6.1) nevertheless has all individual and maximal component
span bounds while contributing at least `n*L_n/8` residual strict short-lag
incidences. Therefore span control does not preserve a uniform constant when
aggregated over event multiplicity.

The additional statistic required by this route is a cluster-multiplicity
bound such as (7.3), not another individual periodic-window length bound.
Nothing here proves or disproves the effective irrationality hypotheses,
(7.3), C7, C2, C1, or the canonical entropy claim for pi.

## 9. Replay

From a directory containing only the delivered artifacts, run

```sh
sh ./verify.sh
```

The replay uses exact Python integers and `fractions.Fraction`. It verifies the
canonical source hash; every event in the first component at scales `6<=n<=40`;
the opposite endpoint using the last full component; count and range formulas
for all intervening translates; and exact rational digits, strict circle
distances, and residual-mask inequalities at scales `6<=n<=10`. It also checks
the lower bound (6.14), explicit witnesses against constants `1,...,20`, and
the finite Fine-Wilf and merge statements for all binary words in stated small
ranges. These finite checks are `experiment`; the universal arguments are the
proof sketch written above. The replay does not recompile the accepted
knowledge-library Lean inputs; Section 10 pins the exact source bytes used.

## 10. Internal source pins

```text
900e9fdeefbaea73236435b3845cd9dcc3c3b07b93d2e244b94dc39f4c109781  T36DecimalPeriodicWindowGap.lean
41e8ec69c4a113592b8f1de1dc5e02e815726c5a7e541ac7fd57afc6b181f1cc  T56LagSectorAudit.lean
1f0a50bc5286e997b897d03d49cc2613370c4cea0a20e41340f099b6278ff174  T2NormalOrbitNearReturns.lean
324478887e8504d8086a9cedc6e640fe415491849e6391b63d1ec3fb10f596d8  T8PiLacunaryNearReturns.lean
cac7b8da11c9369510e2e6e76b8bc74820b50ffe0285310475c7cf8ee1cfe91c  T7FiniteCylinderEnergy.lean
86639d8f8adbb5cf54a474fe89760cbeecd243e9f0bcb3768a16a23dab3ee88c  T25T25ResidualPairReduction.lean
744731fcaa2e252a8f63b0a0bbaf09ea86bdc72f379616437cc5b570f282e6b0  T26T26LongLagResidualReduction.lean
```
