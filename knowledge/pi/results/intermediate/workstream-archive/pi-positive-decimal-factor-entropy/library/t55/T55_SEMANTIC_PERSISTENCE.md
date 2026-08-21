# T55: semantic persistence and moving deviations

Status: `proof sketch` for the new compactness and cross-depth arguments;
`machine-checked` only for the cited T44 and T48 declarations.

## 1. Provenance and scope

- Canonical statement: `knowledge/pi/statements/pi-positive-decimal-factor-entropy.txt`.
- Original source URL: none; the canonical question was formulated locally.
- Verified SHA-256:
  `a70dd741b27595aeb3dfc902b5e201579fed6bae24e2191f58c5ac64a22939e6`.
- Canonical question: whether one fixed `eta > 0` gives
  `p_pi(n) >= 10^(eta*n)` for every sufficiently large `n`.
- T55 concerns a sibling finite-core construction for one fixed forbidden word.
  It does not answer the canonical question.

This note uses the kernel-checked modules

```text
TheoryLib.PiPositiveDecimalFactorEntropy.T44T44EndpointSafeInvariantCore
TheoryLib.PiPositiveDecimalFactorEntropy.T48T48EndpointCarryKMP
```

and does not use T53 as a premise. The depth maps below are defined and argued
directly from T48's definitions in this note.

## 2. Normalized statement and quantifiers

Fix a decimal word

```text
w : List (Fin 10),    hw : w != [].
```

The nonemptiness hypothesis is required by T48's graph. For `w=[]`, T44's
`OccursAt [] a start` is vacuously true, so no stream avoids the empty word and
the premise that every core is infinite is false. Thus excluding the empty
word loses no instance of the semantic implication.

Let `T` be `UnitAddCircle`. For every natural number `R`, put

```text
C_R = Core(w,R) subset T.
```

For a subset `A` of `T`, its derived set is

```text
A' = {z in T : for every real eps > 0, there is y in A
                  with y != z and dist(y,z) < eps}.
```

All balls in this definition are open. This convention is independent of
T44's closed-radius convention for `EpsilonDense`.

The semantic persistence statement is

```text
(for every R : Nat, C_R is infinite)
  -> (there exists z : T, for every R : Nat, z in C_R').       (S)
```

Every quantifier in (S) is displayed. In particular, the same `z` must work
for all depths.

## 3. Machine-checked inputs used

The following are the only substantive T44/T48 facts taken as established.

1. T44 `core_isClosed w R`: `C_R` is closed.
2. T44 `core_antitone_radius w`: if `R <= S`, then `C_S subset C_R`.
3. T48 `graphEvaluation_image_eq_core w hw R`: the image of the full infinite
   label language at depth `R` under graph evaluation is exactly `C_R`.
4. T48 `graphEvaluation_language_fiber_finite w hw R z`: graph evaluation,
   restricted to the depth-`R` infinite label language, has a finite fiber
   over every circle point `z`.
5. T48's definitions of `RawStep`, `Label`, `carryKMPGraph`, and
   `graphEvaluation`, together with its root/raw transition characterizations.

The exact recompiled source pins are

```text
T44T44EndpointSafeInvariantCore.lean
  0157022e5125d130a8e12d1e40e97ee9e3df10fb3aa179c8a1cacbdaace59083
T48T48EndpointCarryKMP.lean
  cbe1652c833fb21ae2618aedbc3040a2f29a7db5b310a9f3873536c888c4b211
```

On 2026-08-02 both files recompiled with `lake env lean`; their printed axioms
for the cited declarations were exactly `propext`, `Classical.choice`, and
`Quot.sound`. The copies supplied in T55's knowledge library had the same
hashes.

The endpoint convention in these facts is literal. Decimal streams may be
all zeroes or all nines, the carry type is the integer interval `[-1,16]`, and
`KWord` uses existence of an avoiding expansion rather than a preferred
half-open expansion.

## 4. The nested-compact-set argument

### Lemma 4.1: an infinite compact metric set has a derived point

Let `K` be an infinite compact subset of a metric space. Choose distinct
points `x_0,x_1,...` in `K`. Compactness gives a convergent subsequence with
limit `z in K`. Every ball about `z` contains a sufficiently late member of
the subsequence different from `z`, so `z in K'`. Hence `K'` is nonempty.

### Lemma 4.2: derived sets are closed and monotone

If `A subset B`, then directly from the quantified definition, `A' subset
B'`.

For closedness, suppose `z` is not in `A'`. Some `eps > 0` satisfies

```text
B(z,eps) intersect (A \ {z}) = empty.
```

Every `u` with `dist(u,z) < eps/3` is also outside `A'`. If `u=z`, this is the
assumption. If `u!=z`, choose a positive ball about `u` that both excludes `z`
and lies inside `B(z,eps)`; that ball contains no point of `A`. Thus the
complement of `A'` is open, and `A'` is closed.

### Theorem 4.3: semantic persistence

Assume every `C_R` is infinite. The circle `T` is compact, and `C_R` is closed
by T44, so `C_R` is compact. Lemma 4.1 makes

```text
D_R = C_R'
```

nonempty. Lemma 4.2 makes `D_R` closed, hence compact. T44 antitonicity and
Lemma 4.2 give

```text
D_(R+1) subset D_R.                                      (4.1)
```

Every finite intersection of the `D_R` is therefore its largest-index member
and is nonempty. Compactness of `T`, or equivalently the finite-intersection
property for closed subsets of `T`, gives

```text
there exists z in intersection over R of D_R.
```

This is exactly (S). Notice that merely intersecting the `C_R` would only give
a common core point. Passing to the nonempty nested sets `C_R'` is what gives
one common non-isolated core point.

## 5. T48 graph spaces and topology

Write

```text
G_R = carryKMPGraph w hw R,
A_R = Label R,
Sigma_R = Nat -> A_R,
L_R = G_R.InfiniteLabelLanguage,
E_R = graphEvaluation : Sigma_R -> T.
```

Give each finite set `A_R` the discrete topology and `Sigma_R` the product
topology. A basic prefix cylinder is

```text
[x|N] = {y : Sigma_R : for every n < N, y(n)=x(n)}.       (5.1)
```

Here `N=0` gives the whole space. Thus “agreement through a prefix of length
`N`” always means agreement at exactly the indices `0,...,N-1`.

The space `Sigma_R` is compact and metrizable. The language `L_R` is closed:
starting from the distinguished root, the partial deterministic transition
recursively reads a label stream. If it never fails, the resulting states and
edges are an infinite-walk witness. If it fails, it does so after a finite
prefix, and the corresponding cylinder is disjoint from `L_R`. Hence `L_R`
is compact.

The map `E_R` is continuous. More quantitatively, if `x` and `y` agree through
their first `N` labels, their coordinate-zero decimal streams agree through
their first `N` digits. The two real decimal values differ by at most

```text
sum from n=N to infinity of 9 / 10^(n+1) = 10^(-N),
```

so their circle distance is at most `10^(-N)`. This estimate includes the
all-nine endpoint stream; no preferred decimal expansion is selected.

## 6. Exact depth truncation

This section derives the maps needed below directly from T48.

### 6.1 One-step maps

For `i : Fin (R+1)`, let `i.up : Fin (R+2)` have the same natural value. For
`j : Fin R`, define `j.up : Fin (R+1)` similarly.

For a depth-`R+1` raw state `q`, define

```text
rho_R(q).kmp(i)   = q.kmp(i.up),       i : Fin (R+1),
rho_R(q).carry(j) = q.carry(j.up),     j : Fin R.
```

Thus `rho_R` deletes only the final KMP coordinate and final carry. On graph
states define

```text
tau_R(none)   = none,
tau_R(some q) = some(rho_R(q)).
```

For a digit column `d : Fin (R+2) -> Fin 10` and a carry tuple
`c : Fin (R+1) -> Carry`, put

```text
delta_R(d)(i) = d(i.up),
gamma_R(c)(j) = c(j.up).
```

The label truncation is

```text
lambda_R(initial(c,d)) = initial(gamma_R(c),delta_R(d)),
lambda_R(next(d))      = next(delta_R(d)).                (6.1)
```

Finally, for `x : Sigma_(R+1)`, define the path truncation pointwise:

```text
Pi_R(x)(n) = lambda_R(x(n)).                              (6.2)
```

### Lemma 6.2: valid transitions project

Suppose `RawStep q d q'` holds at depth `R+1`. Its KMP part consists of one
valid KMP transition for each coordinate `0,...,R+1`. Restricting to
`0,...,R` gives the KMP part of `RawStep (rho_R q) (delta_R d) (rho_R q')`.
Its carry part consists of

```text
16*d_j + c'_j = d_(j+1) + 10*c_j
```

for `j=0,...,R`. Restricting to `j=0,...,R-1` gives exactly the lower-depth
carry part. Therefore raw steps project.

For a root edge, T48 `transition_from_root` exposes an initial label and a raw
step from `initialRaw`. Restriction commutes with `initialRaw`: all retained
KMP coordinates are initial and the retained carry tuple is `gamma_R(c)`.
T48 `transition_initial_eq_some_iff` then gives the projected root edge. For an
edge from a raw state, use `transition_from_raw`, the preceding raw-step
restriction, and `transition_next_eq_some_iff`. The two other source/label
combinations are invalid at both depths. Hence every valid high edge projects
to a valid low edge, with source and target mapped by `tau_R`.

### Corollary 6.3: paths and evaluation project

Project each edge of an infinite high walk. Lemma 6.2 preserves validity, and
the projected target of one edge is the projected source of the next. The
root is fixed. Consequently

```text
x in L_(R+1) -> Pi_R(x) in L_R.                           (6.3)
```

The zero coordinate is retained by `delta_R`, so definitionally

```text
E_R(Pi_R(x)) = E_(R+1)(x).                               (6.4)
```

For `R <= S`, let `Pi_(R,S)` be the composite of the one-step maps from depth
`S` down to depth `R`; `Pi_(R,R)` is the identity. Equations (6.3)-(6.4) hold
for every `Pi_(R,S)` by induction.

No converse path-lifting or surjectivity assertion is used.

## 7. Moving-deviation graph statement

For `x in L_R`, define the path-only late-deviation property

```text
Late_R(x) :<->
  for every N : Nat, there exists y : Sigma_R such that
    y in L_R,
    (for every n : Nat, n < N -> y(n)=x(n)),
    y != x.                                               (7.1)
```

The witness `y` may depend on both `R` and `N`. Equation (7.1) says that its
first deviation, which exists because `y!=x`, occurs at an index at least
`N`. It does not require one common deviating path for different cutoffs.

The exact compatible all-depth graph statement is

```text
there exist
  z : T and
  X : (for every R : Nat, Sigma_R)
such that
  for every R : Nat,
    X_R in L_R,
    E_R(X_R) = z,
    Late_R(X_R),
and
  for every R : Nat,
    Pi_R(X_(R+1)) = X_R.                                 (G)
```

Thus (G) is one compatible all-depth path, represented as one path at every
finite depth. The equalities `E_R(X_R)=z` are stated explicitly even though
they also follow from compatibility and (6.4) once the depth-zero value is
fixed.

### Lemma 7.2: path deviations can be made evaluation-distinct

For `x in L_R` with `E_R(x)=z`, T48
`graphEvaluation_language_fiber_finite` says

```text
F = {y in L_R : E_R(y)=z}
```

is finite. For every `y in F \ {x}`, choose one index at which `y` and `x`
differ. Because there are only finitely many such `y`, there is a prefix
length `N_0` for which no member of `F \ {x}` agrees with `x` through length
`N_0`. If `F={x}`, take `N_0=0`.

It follows that `Late_R(x)` is equivalent to

```text
EvalLate_R(z,x) :<->
  for every N : Nat, there exists y : Sigma_R such that
    y in L_R,
    (for every n < N, y(n)=x(n)),
    E_R(y) != z.                                         (7.2)
```

The forward implication applies (7.1) at `max(N,N_0)`; its witness cannot lie
in `F`. The reverse implication is immediate because different evaluations
imply different paths.

This is the point where endpoint fibers matter. Merely declaring distinct
paths to have distinct circle values would be false at decimal endpoints.
T48's finite-fiber theorem supplies the valid replacement.

## 8. Equivalence of semantic and graph persistence

Define the unconditioned semantic assertion

```text
Sem(w) :<-> there exists z : T, for every R, z in C_R'.  (8.1)
```

### Theorem 8.2: (G) implies `Sem(w)`

Assume (G), and fix `R` and `eps>0`. By Lemma 7.2, choose a cutoff `N` large
enough that `10^(-N)<eps` and a path `y in L_R` agreeing with `X_R` through
length `N` such that `E_R(y)!=z`.

T48 `graphEvaluation_image_eq_core` gives `E_R(y) in C_R`. Section 5 gives

```text
dist(E_R(y),z) = dist(E_R(y),E_R(X_R))
               <= 10^(-N) < eps.
```

Thus `z in C_R'`. Since `R` was arbitrary, `Sem(w)` holds. This direction
checks both graph-to-evaluation requirements: graph membership places the
evaluation in the core, and increasingly long common prefixes force circle
values to converge even at endpoints.

### Lemma 8.3: each derived core point has an accumulation lift

Assume `z in C_R'`. Define

```text
M_R(z) = {x in L_R : E_R(x)=z and EvalLate_R(z,x)}.       (8.2)
```

This set is nonempty. Indeed, choose `z_k in C_R \ {z}` with
`dist(z_k,z)<1/(k+1)`. By T48's exact graph-image theorem, choose
`y_k in L_R` with `E_R(y_k)=z_k`. Compactness of `L_R` gives a convergent
subsequence with limit `x in L_R`. Continuity gives `E_R(x)=z`. For every
prefix length `N`, convergence in the finite-alphabet product topology makes
a sufficiently late `y_k` agree with `x` through that prefix, while
`E_R(y_k)=z_k!=z`. Hence `x in M_R(z)`.

The set is also compact. If

```text
F_R(z) = L_R intersect E_R^(-1)({z}),
```

then the quantified prefix condition gives the exact identity

```text
M_R(z) = F_R(z) intersect closure(L_R \ F_R(z)).         (8.3)
```

Both factors on the right are closed in compact `Sigma_R`.

### Lemma 8.4: accumulation lifts project

For every `R`,

```text
Pi_R(M_(R+1)(z)) subset M_R(z).                          (8.4)
```

Take `x in M_(R+1)(z)`. Equations (6.3)-(6.4) put `Pi_R(x)` in `L_R` with
evaluation `z`. Given `N`, choose the high-depth witness `y` in (7.2).
The paths `Pi_R(y)` and `Pi_R(x)` agree through `N`, and (6.4) preserves the
inequality `E_(R+1)(y)!=z`. Thus `Pi_R(x) in M_R(z)`.

### Theorem 8.5: `Sem(w)` implies (G)

Assume `Sem(w)` and fix its common point `z`. Lemma 8.3 gives a nonempty
compact space `M_R(z)` for every `R`, and Lemma 8.4 gives continuous bonding
maps between consecutive spaces.

Consider the compact product

```text
P = product over R of M_R(z).
```

For each `R`, the compatibility constraint

```text
Pi_R(X_(R+1)) = X_R                                    (8.5)
```

is closed in `P`. Every finite family of these constraints is satisfiable:
if `S` is larger than every depth appearing in the family, choose any
`x_S in M_S(z)`, define all required lower coordinates by the composites
`Pi_(R,S)(x_S)`, and choose arbitrary elements at unused higher coordinates.
Lemma 8.4 keeps every projected coordinate in its required `M_R(z)`.

The finite-intersection property in compact `P` therefore supplies `X`
satisfying every constraint (8.5). Membership of `X_R` in `M_R(z)` gives
`X_R in L_R`, `E_R(X_R)=z`, and `EvalLate_R(z,X_R)`, hence `Late_R(X_R)` by
Lemma 7.2. This is precisely (G).

Combining Theorems 8.2 and 8.5 gives

```text
Sem(w) <-> (G).                                         (8.6)
```

Combining Theorem 4.3 with (8.6) proves the requested conditional graph
consequence:

```text
(for every R, Core(w,R) is infinite) -> (G).             (8.7)
```

## 9. Endpoint audit

The proof never chooses a canonical decimal expansion.

1. T44 cores use `KWord`, whose membership is existential in an avoiding
   decimal expansion.
2. T48's exact image theorem supplies every core point from the
   endpoint-complete graph and sends every graph path back into the core.
3. Depth truncation retains every carry in `[-1,16]`; it does not remove the
   endpoint carries `-1` or `16`.
4. Prefix convergence is applied to the selected graph paths, where it is
   valid even for the all-nine stream.
5. Distinct graph paths are not presumed to have distinct evaluations.
   Lemma 7.2 uses T48's finite language-fiber theorem to move beyond all
   same-evaluation alternatives before invoking derived-set semantics.

Thus neither direction fails because of decimal endpoints or evaluation
fibers.

## 10. Conditional scope and claim ledger

- `machine-checked`: the four named T44/T48 facts in Section 3, with their
  exact Lean statements and allowed axioms.
- `proof sketch`: Theorem 4.3, the direct depth-projection proof, and the
  semantic/graph equivalence (8.6).
- No new Lean theorem is claimed for T55.
- Conditional conclusion only: if one fixed nonempty word has infinite core
  at every depth, then it has the semantic and graph persistence objects.
- No existence claim: this note does not exhibit or prove the hypothesis for
  any word.
- No extinction claim: it neither proves nor refutes universal linear
  finite-core extinction. If the displayed hypothesis were later established
  for a word, failure of finite-core extinction for that word would be a
  conditional consequence.
- No C6 claim: T44 gives a sufficient implication from a universal linear
  finite-core hypothesis to C6, not a converse. Persistence cannot be used to
  infer failure of C6.
- No C1 or pi-entropy claim: neither (S), (G), nor their equivalence proves or
  refutes C1, positive decimal factor entropy, disjunctivity, or any assertion
  about the decimal expansion of pi.
