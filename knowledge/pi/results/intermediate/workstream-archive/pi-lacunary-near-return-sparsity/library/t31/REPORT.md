# T31: moving-root compactness for decimal count trees

Status: `proof sketch`. The imported T14 and T29 declarations identified
below are `machine-checked`; the new compactness and pullback arguments are
numbered prose and are not claimed to be machine-checked.

## 1. Provenance and scope

- Canonical statement: `knowledge/pi/statements/pi-lacunary-near-return-sparsity.txt`.
- Original source URL: none; the canonical question is local and was
  formulated by this program on 2026-07-22.
- SHA-256, rechecked on 2026-07-24:
  `cbf56699b651aeb69301265763e38da44feb59c6fd955d2280887e8c06c6a2f8`.
- The canonical question asks whether, for every integer `A >= 1`, every
  sufficiently large integer `n` admits an integer `N >= 1` such that
  `A*n*Q_pi(n,N) <= N^2`, with ordered pairs and the diagonal included.
- T31 concerns an abstract A14 decimal count-tree interface. It does not prove
  C2, canonical A1, or any unconditional assertion about pi.

The purpose is to decide exactly what remains when long finite paths begin at
depths which are not uniformly bounded. The answer is two-part: recentering
does give an infinite branch in a tangent count tree, but this does not give a
branch in the original rooted tree. The exact pullback premise is anchored
fixed-predicate tightness, defined in Section 6.

## 2. Normalized definitions and ambiguous quantifiers

Let `D={0,1,...,9}`. Let `D^n` be the words of length `n`, let `D^*` be all
finite words, and write `uv` for concatenation. The empty word is `e`.

### 2.1 Count trees

A nonnegative decimal count tree through depth `s` is a family

```text
c(w) in the nonnegative reals,  w in D^n, 0 <= n <= s,
```

satisfying, for every `n<s` and every `w in D^n`,

```text
c(w) = sum_{a in D} c(wa).                         (C)
```

Integer-valued trees are the specialization used for finite orbit counts.
Real-valued trees are needed after normalization and are explicitly supported
by T29's `DecimalCounts` and `IsFiniteDecimalCountTree`.

For a level `n`, define the ordered, diagonal-inclusive collision energy

```text
E_c(n) = sum_{w in D^n} c(w)^2.                    (E)
```

For `0<alpha<=1`, call `w -> wa` a positive `alpha`-dominant edge when

```text
c(w)>0 and c(wa) >= alpha*c(w).                    (G)
```

The positivity clause excludes vacuous zero-to-zero paths. It should be
encoded in the edge predicate when applying T29's generic compactness theorem.

### 2.2 Triangular moving-root data

For every row index `q in N`, the data are:

1. integers `s_q`, `r_q`, and `h_q` with `r_q+h_q<=s_q`;
2. a count tree `c_q` through depth `s_q`;
3. a word `u_q in D^(r_q)` with `c_q(u_q)>0`;
4. digits `a_(q,0),...,a_(q,h_q-1)` defining
   `x_(q,0)=u_q` and `x_(q,i+1)=x_(q,i)a_(q,i)`;
5. a number `alpha_q in (0,1]` such that every displayed edge is positive
   `alpha_q`-dominant.

The length condition is the full eventual quantifier

```text
for every H in N, there is q_0 such that
for every q>=q_0, h_q>=H.                          (L)
```

Thus `h_q -> infinity`; merely having unbounded lengths is weaker, although an
unbounded sequence can first be replaced by a subsequence satisfying (L).
Starting-depth escape means

```text
for every R in N, there is q_0 such that
for every q>=q_0, r_q>R.                          (S)
```

The compactness theorem below does not require (S). It permits it. The
counterexample satisfies it.

### 2.3 Meaning of low leakage

Fix a row and consecutive levels `r,...,r+h-1`. Let `G_n` be positive
dominant parents, choose one qualifying child of every parent in `G_n`, and
put

```text
R_n = sum_{w in G_n} c(w d_n(w))^2,
L_n = E_c(n)-R_n.                                 (F)
```

This is T29's full selected-edge leakage, not just mass outside dominant
parents. A row is `Lambda`-low-leakage when

```text
sum_{i=0}^{h-1} L_(r+i) <= Lambda*E_c(r),
0<=Lambda<1.                                      (LL)
```

For real-valued trees, T29's machine-checked
`exists_endpoint_with_retained_mass`, together with its exact `SurvivorStep`,
says that (LL), positivity of `E_c(r)`, and the stated conservation hypotheses
leave a nonempty survivor at `r+h`, since `Lambda<1` makes the required total
leakage inequality strict. Its
`finite_base10_countTree_retained_fraction` gives the displayed normalized
form (LL) directly for natural counts. Tracing a survivor's predecessor
through the successor-image equations gives a genuinely nested selected path
of length `h`. T29's machine-checked `selected_path_retains_product` then gives
the product retention bound along that path.

### 2.4 Ambiguities resolved

1. A path length counts edges, so a length-`h` path has `h+1` nodes.
2. Every selected level is consecutive: exactly `r,...,r+h-1`.
3. Rows may have different count trees, cutoffs, roots, and starting depths.
4. A subsequence below always means a strictly increasing map
   `phi:N->N`.
5. Tangent coordinates are suffix words relative to `u_q`; they are not
   words at a fixed absolute depth in the original tree.
6. Convergence is coordinatewise for every fixed suffix word after the row is
   deep enough to contain it.
7. Dominant branches are positive; zero-count branches are excluded.
8. Pullback concerns one fixed edge predicate on one fixed original rooted
   tree. Varying cutoffs or thresholds do not satisfy that requirement.

## 3. Moving-root compactness theorem

For `|v|<=h_q`, define the normalized recentered profile

```text
p_q(v) = c_q(u_q v)/c_q(u_q).                     (Pq)
```

Conservation and `c_q(u_q)>0` imply

```text
p_q(e)=1,
0<=p_q(v)<=1,
p_q(v)=sum_{a in D} p_q(va) whenever |v|<h_q.     (PCq)
```

**Theorem 1 (moving-root compactness).** Assume the triangular data of Section
2, (L), and `alpha_q -> alpha` for some `alpha in [0,1]`. Then there are a
strictly increasing `phi:N->N`, digits `a_0,a_1,...`, and a function
`p:D^*->[0,1]` such that:

```text
p(e)=1;                                           (T1)
p(v)=sum_{a in D} p(va) for every v in D^*;       (T2)
for every fixed v,
  p_(phi(j))(v) -> p(v) as j->infinity;           (T3)
for every i, there is J_i such that
  a_(phi(j),i)=a_i for every j>=J_i;               (T4)
p(a_0...a_i) >= alpha*p(a_0...a_(i-1))            (T5)
  for every i>=0,
```

where the right side of (T5) at `i=0` is `alpha*p(e)`.

If `alpha_q -> 1`, then

```text
p(a_0...a_(i-1))=p(a_0...a_i)=1 for every i.      (A)
```

Consequently `a_0a_1...` is an infinite positive dominant branch in the
tangent count tree `p`, at threshold `1` and hence at every threshold at most
`1`.

### Proof of Theorem 1

1. The set `D^*` is countable. Enumerate it as `v_0=e,v_1,v_2,...`, in an
   order nondecreasing in word length.
2. By (L), for each fixed `m`, all sufficiently late rows define `p_q(v_i)`
   for every `i<=m` and define the first `m` path digits.
3. The first path digit lies in the finite set `D`, so an infinite subsequence
   makes it constant. The bounded real coordinate `p_q(v_0)` has a convergent
   subsequence by Bolzano-Weierstrass. Repeat successively for digit `i` and
   coordinate `v_i`, always taking a subsequence of the preceding one.
4. Take the diagonal subsequence: its `j`-th term is the `j`-th term of the
   `j`-th nested subsequence. It can be thinned once more to make its original
   row indices strictly increasing. Call those indices `phi(j)`.
5. For each fixed `i`, all diagonal terms after stage `i` belong to the
   subsequence on which digit `i` is constant and coordinate `v_i` converges.
   This proves (T3) and (T4), simultaneously for every fixed coordinate and
   digit. This is one subsequence, not a separate subsequence for each depth.
6. Define `p(v_i)` as the limit in (T3). Since every `p_q(v_i)` lies in
   `[0,1]`, so does `p(v_i)`, and `p(e)=1`.
7. Fix `v`. For all sufficiently large `j`, (PCq) holds at `v`. Taking limits
   commutes with the sum of exactly ten terms, proving (T2).
8. Fix `i`. For all sufficiently large `j`, the first `i+1` row digits have
   stabilized to `a_0,...,a_i`, and row dominance gives
   `p_(phi(j))(a_0...a_i) >= alpha_(phi(j))
   p_(phi(j))(a_0...a_(i-1))`. Taking limits proves (T5).
9. If `alpha=1`, conservation and nonnegativity give
   `p(va)<=p(v)` for every child. Combined with (T5), equality holds on the
   selected edge. Starting from `p(e)=1`, induction gives (A).

This proves the tangent conclusion. Notice that neither `r_q` nor `u_q`
appears in the limiting coordinate names; both were erased by recentering.

## 4. Low-leakage input and the checked T14/T29 route

This section records precisely what the two kernel-checked dependencies do and
does not promote any unverified note to a premise.

### 4.1 T29

The following T29 declarations are machine-checked:

1. `finite_base10_countTree_mass_conservation` proves exact mass conservation.
2. `collisionEnergy_succ_le` proves energy monotonicity under nonnegative
   conservative refinement.
3. `leakage_le_explicit` proves

   ```text
   L_n <= [1-alpha^2(1-mu)] E_c(n)                (B)
   ```

   from dominant-parent energy at least `(1-mu)E_c(n)` and selected-child
   retention at least `alpha`.
4. `finite_base10_countTree_retained_fraction` proves the nonempty endpoint
   consequence of (LL), with every finite-tree, start, length, and survivor
   compatibility hypothesis explicit.
5. `exists_infinite_good_branch_of_bounded_starts` proves compactness for one
   fixed finite-level edge predicate when all starts are bounded.

### 4.2 T14, only under its literal premise

T14's machine-checked
`not_piPolynomialSmallBallC2_implies_failure_and_weighted_dominance` says:
conditional on literal `not C2`, for every admissible fixed tuple
`(mu,eta,d,B,m0,k0,N,nu)` satisfying all displayed monotonicity, positivity,
and weak-convergence hypotheses, there are `k>=k0` and `m` with
`m0<=m<=k` such that

```text
S := piSplittingLevelCount(m,N(k),mu,eta) < d*m-B, (T14a)
```

and every nonsplitting `l<m` satisfies the strict weighted-dominance bound

```text
(1-mu)E_l < D_l.                                 (T14b)
```

T14 itself explicitly makes no common or nested branch claim.

### 4.3 Conditional production of arbitrarily long low-leakage rows

First identify the T14 cylinder counts with an exact T29 count tree. For every
fixed cutoff `K>=1`, set

```text
c_K(n,a)=card(piCylinderFiber(n,K,a)).             (CK)
```

The required bridge, including all T29 hypotheses, is as follows.

1. T9's checked `piCylinderFiber_card_eq_sum_successorCount` gives
   `c_K(n,a)=sum_d piSuccessorCount(n,K,a,d)`.
2. The definitions of `piCylinderCode`, `prefixLabel`, and successor fiber,
   together with the decimal identity
   `wordValue(w appended d)=10*wordValue(w)+d`, give the exact set equality

   ```text
   piSuccessorFiber(n,K,a,d)
     = piCylinderFiber(n+1,K,decimalChild(n,a,d)). (CF)
   ```

   Indeed, membership on either side says that the first `n` digits have
   code `a` and the next digit is `d`; T29's checked
   `decimalChild_val` is exactly `d+10*a`. Taking cardinalities in (CF) and
   substituting in Step 1 proves

   ```text
   c_K(n,a)=sum_d c_K(n+1,decimalChild(n,a,d)).    (CC)
   ```

   Thus `c_K` satisfies T29's `IsFiniteBase10CountTree` through every stated
   finite depth. Nonnegativity is automatic because the counts are natural.
3. At each selected level define `dominant(n,a)` to be T9's
   `HasDominantSuccessor(n,K,eta,a)`. Choose one witnessing digit whenever
   this holds, and choose digit `0` otherwise. With (CK), T29's
   `dominantParentEnergy` is term-for-term T9's
   `piDominantSuccessorEnergy`, and the chosen-edge inequality is exactly the
   witness in `HasDominantSuccessor`.
4. At the selected start `r`, set the survivors equal to T29's
   `positiveSupport c_K.toReal r`. Recursively, for each selected level, set
   the next survivor set to the image of the current dominant survivors under
   the chosen decimal child. These are exactly the equations required by
   `SurvivorStep`; `positiveSupport_energy_eq` gives the required initial
   survivor-energy equality.
5. The unique level-zero cylinder has count `K>0`. Conservation therefore
   makes every total level mass positive, so `E_(c_K)(r)>0`. Moreover a
   survivor starts positive and each selected edge has positive retention
   factor, so every node on a surviving path remains positive.

Now fix `H>=1`. Instantiate the checked T14 implication, still conditional on
literal `not C2` and all its other inputs, with

```text
mu_H=eta_H=1/(100H), d_H=1/(2H), B=0, m0=2H.     (Q)
```

The following argument is included here rather than imported from any prose
note. Apply the bridge above with `K=N(k_H)` after T14 selects `k_H`.

6. T14 gives `m>=2H` and an integer `S<m/(2H)`.
7. If the levels `0,...,m-1` contained no run of `H` consecutive
   nonsplitting levels, each of the `floor(m/H)` disjoint full blocks of length
   `H` would contain a splitting level. Thus
   `S>=floor(m/H)>=m/H-1>=m/(2H)`, a contradiction.
8. Let `r_H,...,r_H+H-1` be such a nonsplitting run in the row with cutoff
   `N(k_H)`. Put `alpha_H=1-9eta_H`.
9. The strict T14 bound (T14b), selection of an `alpha_H`-dominant child, and
   T29's bound (B) give, at every level of the run,

   ```text
   L_n < delta_H E_n,
   delta_H=1-(1-mu_H)(1-9eta_H)^2.
   ```

10. With `x=1/(100H)`, direct expansion gives

   ```text
   (1-x)(1-9x)^2=1-19x+99x^2-81x^3 >= 1-19x,
   delta_H<=19/(100H).                           (D)
   ```

11. T29 energy monotonicity gives `E_(r_H+i)<=E_(r_H)`. Therefore

   ```text
   sum_{i=0}^{H-1} L_(r_H+i)
     < H delta_H E_(r_H)
     <= (19/100) E_(r_H).                        (R)
   ```

12. Since `19/100<1`, the concrete tree, survivor sets, and positivity checks
   in Steps 1-5 discharge every hypothesis of T29's retained-fraction theorem.
   It gives a nonempty survivor endpoint. The defining `SurvivorStep`
   equations recursively supply its selected predecessors, hence a nested
   path of length `H`.
13. Every edge of that path retains at least `alpha_H`, and
   `alpha_H=1-9/(100H)->1`. Applying Theorem 1 to any resulting sequence of
   rows gives an atomic infinite dominant branch in a tangent count tree.

This is a conditional tangent obstruction only. The cutoffs `N(k_H)`, starts
`r_H`, roots, and predicates depend on `H`; no fixed original branch follows.
In particular, this section does not assert `not C2`.

## 5. Exact triangular counterexample to pullback

The next single real count tree has zero-leakage paths of every length whose
starts tend to infinity, while its fixed positive `1/2`-dominant predicate has
no infinite branch. Thus even a fixed count tree is not enough without start
tightness.

Define

```text
b_H=(H-1)(H+2)/2,                    H>=1,
B_H={b_H,b_H+1,...,b_H+H-1},
s_H=b_H+H=b_(H+1)-1.
```

The edge levels are partitioned into the good blocks `B_H` and separator
levels `s_H`. Define `c(e)=1` recursively for every finite word `w` of length
`n`:

```text
if n is in some B_H:
    c(w0)=c(w), and c(wa)=0 for a!=0;
if n=s_H for some H:
    c(wa)=c(w)/10 for every a in D.               (X)
```

### Exact verification

1. Nonnegativity is immediate from (X).
2. At a good level, the child sum is `c(w)+9*0=c(w)`. At a separator,
   the child sum is `10*(c(w)/10)=c(w)`. Hence (C) holds at every node.
3. At a good level, every positive parent has exactly one positive child,
   with ratio `1`. Its selected-edge energy equals its parent energy, so the
   full leakage (F) is exactly zero.
4. Therefore the path beginning at any positive `u_H in D^(b_H)` and taking
   digit `0` for the next `H` edges is a zero-leakage positive
   `1/2`-dominant path of length `H`.
5. The starts diverge because `b_H=(H^2+H-2)/2 -> infinity`.
6. At every separator level, every child of a positive parent has ratio
   exactly `1/10<1/2`. Thus no positive `1/2`-dominant edge crosses a
   separator.
7. For every proposed starting depth `r`, there is a separator `s_H>=r`.
   Any infinite path from depth `r` must cross the edge level `s_H`, where no
   positive dominant edge exists. Hence the original tree has no infinite
   positive `1/2`-dominant branch from any start.
8. Recenter the length-`H` path at `u_H`. For every `|v|<=H`, its profile is

   ```text
   p_H(v)=1 if v=0^|v|, and p_H(v)=0 otherwise.
   ```

   Thus the profiles already agree on every common finite window. Their
   tangent is the conservative count tree concentrated on `000...`, which has
   an infinite threshold-`1` dominant branch.

This checks all conservation, start-depth, and branch assertions exactly. The
tangent branch is `000...` in suffix coordinates. It is not an original
dominant branch: every attempted original path encounters a separator.

## 6. Exact pullback condition

Let `Node(n)` be finite for every `n`, and fix one edge predicate
`G_n subset Node(n) x Node(n+1)` outside every length quantifier. Define

```text
Anchored(G) :<=> there exists R in N such that
  for every H in N, there exist r<=R and nodes x_0,...,x_H
  with x_i in Node(r+i) and G_(r+i)(x_i,x_(i+1)) for i<H.   (AT)
```

**Theorem 2 (exact pullback criterion).** For finite levels,

```text
Anchored(G)
  <=> there exist r and x_0,x_1,... forming an infinite G-branch. (PB)
```

### Proof of Theorem 2

1. Assume (AT), and fix its `R`. This is literally T29's machine-checked
   hypothesis for `exists_infinite_good_branch_of_bounded_starts`, with
   `startBound=R`, `edge=G`, and each finite witness represented by
   `GoodPrefix`. T29 yields a start `r<=R` and an infinite `G`-branch.
2. Conversely, given an infinite branch starting at `r`, take `R=r` and its
   first `H` edges for each `H`. This proves (AT).

For decimal pullback, `G` must additionally encode one fixed count tree or
cutoff, one fixed threshold, literal decimal-child compatibility, and
positivity if a nonzero mass branch is intended. This is the exact tightness
condition: bounded starts alone is insufficient if the predicate changes
between rows, and a fixed predicate alone is insufficient if starts escape.

T29 packages the fixed-pi-shaped sufficient premise as
`T14MissingBoundedFixedPredicatePremise cutoff startBound eta`; its checked
`t14_failure_and_compactness_interface` deliberately requires that premise
separately. T14 does not supply it. The counterexample in Section 5 fails (AT):
among the finitely many starts `r<=R`, the distance to the next separator is
uniformly bounded, so paths from those starts cannot have arbitrary length.

## 7. Reproduction

From this artifact directory run:

```sh
python3 -B verify_counterexample.py
```

The script uses exact `fractions.Fraction` arithmetic. Over a finite range it
verifies the block partition, conservation on the full positive support,
energy and leakage identities, increasing starts, all finite-window tangent
profiles, and the separator obstruction. Conservation at every zero parent is
the immediate symbolic consequence of (X): once a nonseparator digit makes a
count zero, all descendants remain zero. The computations support the
explicit example; the universal claims are established by the numbered
symbolic arguments above, not by finite testing.

## 8. Verdict

Moving-root compactness is valid after normalizing each positive root and
passing to one diagonal subsequence. In the T14/T29 low-leakage regime where
`alpha_H->1`, the tangent contains an atomic infinite dominant branch.
Recentring erases absolute depths, ancestors, and row-dependent predicates,
so this branch does not pull back automatically. The necessary and sufficient
additional condition for a fixed finite-level predicate is (AT), equivalently
T29's bounded-start arbitrarily-long-prefix premise. The exact conservative
tree (X) proves that divergent zero-leakage witnesses can fail this condition
and have no original positive dominant branch.

No C2, canonical A1, or unconditional pi claim is made.

Under the program's claim vocabulary, this artifact remains a `proof sketch`,
not `machine-checked`. The required terminal verdict records that the numbered
prose theorem and exact counterexample have no named mathematical gap; it does
not upgrade their verification label.

**PROVED**
