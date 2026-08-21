# T39: bounded pullback literature audit

Status: `literature-checked` source audit; no mathematical property of pi is
asserted.

Verdict: **no retained theorem applies unconditionally to pull T14/T33 moving
roots back to one original-coordinate branch.** One quasi-Bernoulli theorem is
`CONDITIONAL` and yields one precise formalization target under a uniform
single-measure comparison premise absent from the checked interfaces.

## 0. Scope and immutable statement

The retained canonical statement is `canonical_statement.txt`, SHA-256

```text
cbf56699b651aeb69301265763e38da44feb59c6fd955d2280887e8c06c6a2f8.
```

It asks the ordered, diagonal-inclusive fixed-pi A1 question

```text
forall A >= 1, exists n0 >= 1, forall n >= n0, exists N >= 1,
  A*n*Q_pi(n,N) <= N^2.
```

T39 neither assumes nor proves this statement. It makes no C2 claim and no
claim about canonical A1. The only artificial-stream result used below is the
kernel-checked T37 boundary for its explicitly constructed A14 sibling; it is
not reported as a fact, model, or empirical observation about pi.

The source search is deliberately bounded to one retained result in each
requested family:

1. the nearest tree-martingale-family boundary candidate, a source-pinned
   conditional-flow/derived-tree compactness theorem;
2. quasi-Bernoulli Gibbs measures;
3. tangent/scenery distributions;
4. symbolic-language compactness.

`SOURCE_PINS.md` records URLs, DOI data, hashes, and exact page/extract
locators. No broader novelty or completeness claim is made.

## 1. Verdict vocabulary and ordered tests

Each verdict is checked in this order. "First unmatched" always means the
first failure in this fixed order, so it is reproducible rather than rhetorical.

**S: start-depth anchoring.** A pullback theorem must either retain one
absolute original root or derive a uniformly bounded set of starts before
passing to a subsequence. Merely identifying each moving root with coordinate
zero fails S.

**P: predicate stability.** The edge predicate, language, or reference
measure must be fixed outside path-length and row quantifiers. A predicate
depending on cutoff, checkpoint, threshold, or row fails P unless the theorem
provides a uniform transport to one fixed predicate.

**M: mass tightness.** Normalized root mass `1` alone is insufficient. The
theorem must preserve nonzero original mass, or provide a uniform distortion
comparison strong enough to transfer positivity and edge ratios from every
normalized row to one original measure.

**B: branch quantifiers.** For one fixed original mass tree, the conclusion
needed here has the shape

```text
exists root, exists continuation, forall depth i, Edge(root, continuation, i)
```

For changing finite rows, the stronger stable form is

```text
exists root, exists continuation, forall i, exists Q, forall q >= Q,
  RowEdge(q, root, continuation, i).
```

A theorem must state which of these targets it reaches. A fixed-measure branch
does not imply the stable changing-row form. A branch only in a recentered
tangent, a derived tree, or a shift orbit reaches neither form and fails B.

Verdicts mean:

- `APPLIES`: the checked input supplies every source hypothesis and the source
  conclusion has the required original-coordinate branch quantifiers.
- `CONDITIONAL`: one explicit additional premise makes the theorem usable,
  and the resulting conditional conclusion is stated exactly.
- `DOES NOT APPLY`: a checked hypothesis or conclusion fails; the first
  unmatched test is recorded.

## 2. Exact checked interfaces

The following are kernel-checked facts from the files pinned in
`DEPENDENCIES.sha256`.

### T14

`T14FailureAndWeightedDominance` is defined at
`FiniteCountTreeLeakage.lean:681--692`, reflecting T14's theorem at
`CoherentSuccessorSplitting.lean:631--655`. Its order is

```text
forall fixed admissible parameters and candidate prefix sequence N,
  exists row k, exists depth m,
    bad splitting count and
    forall l < m, nonsplitting(l) -> weighted dominance(l, N(k)).
```

It does not quantify an edge-compatible finite path, a common start, or a
single cutoff valid for all lengths. The T14 source comment explicitly says
"No common or nested branch is claimed."

### T29

`exists_infinite_good_branch_of_bounded_starts`,
`FiniteCountTreeLeakage.lean:590--648`, assumes finite node types, one `edge`
fixed outside all length quantifiers, one `startBound`, and

```text
forall length, exists start <= startBound,
  Nonempty (GoodPrefix Node edge start length).
```

It concludes

```text
exists start <= startBound, exists node,
  forall i, edge (start+i) (node i) (node (i+1)).
```

This is already the exact generic original-coordinate compactness theorem.
`T14MissingBoundedFixedPredicatePremise`, lines 663--667, names the premise
not supplied by T14. T29's leakage theorems separately require explicit
`SurvivorStep` compatibility; small full-level leakage does not synthesize it.

### T33

`exists_movingRoot_tangent_branch`, `MovingRootTangent.lean:90--201`, assumes
window lengths eventually exceed each fixed `H` and thresholds tend to fixed
positive `alpha`. Each row has its own `count`, `root`, `startDepth`, and
digits. It concludes a subsequential normalized suffix profile and branch.
The absolute roots and starts do not occur in that branch conclusion.

`separatorBlock_tangent_does_not_pull_back`, lines 581--613, gives one
conservative abstract tree with escaping starts, arbitrarily long moving-root
half-dominant windows, and a tangent branch, while every original root and
continuation eventually crosses a separator. This is a kernel-checked abstract
A14 boundary, not a statement about pi.

### T37

`StableOriginalBranch`, `ArtificialStreamObstruction.lean:1692--1703`, expands
the exact stable quantifier order

```text
exists root, exists continuation, forall i, exists Q, forall q >= Q,
  beta * count_q(root ++ prefix_i) <= count_q(root ++ prefix_(i+1))
  and positive parent mass.
```

`artificialStream_obstruction`, lines 1810--1844, combines vanishing normalized
moving-window leakage and a moving-root tangent branch with
`not StableOriginalBranch (1/2)` for one explicit artificial decimal stream.
Its roots, checkpoints, thresholds, and selected successor choices vary with
stage. This result concerns only that construction and never pi.

## 3. Source theorem audit

### S1. Tree-martingale-family audit: Lyons--Peres 15.20: `DOES NOT APPLY`

The theorem starts from one uniformly bounded-degree tree and produces a unit
flow on a derived tree `T* in D(T)`. By the source definition, descendant root
`v` is identified with the new root and the conditional flow is divided by
`theta(v)`.

This is a unit-flow/derived-tree theorem, not a martingale convergence theorem.
It is retained as the closest theorem in the tree-martingale/boundary family
because the displayed conditional-flow operation is exactly the moving-root
normalization at issue. The audit does not infer a branch from generic scalar
martingale convergence.

| Test | Result | Reason |
|---|---|---|
| S | FAIL | Moving vertices may escape and are explicitly recentered. |
| P | PASS only for its own input | All descendants come from one fixed tree. T14/T37 do not supply one fixed good-edge tree. |
| M | FAIL for pullback | The theorem supplies no comparison between its separately constructed unit flows and mass at the original root. |
| B | FAIL | The ray and flow live on `T*`, not at one absolute root of `T`. |

**First unmatched hypothesis/conclusion: S, start-depth anchoring.** Uniform
degree is not the problem: the decimal tree has degree ten. The theorem is a
strong tangent/derived-tree result, but its own definitions show why it cannot
perform the requested pullback.

### S2. Feng--Lau, Theorem 1.1 and (1.4): `CONDITIONAL`

For one primitive finite-type shift and one Holder-continuous strictly positive
matrix potential, the source constructs one invariant Gibbs probability
measure `mu` and proves one constant `C` such that every admissible
concatenation satisfies

```text
C^-1 mu([u]) mu([v]) <= mu([uv]) <= C mu([u]) mu([v]).   (QB)
```

For `mu([u]) > 0` and admissible `u`, `v`, and `uv`, the conditional suffix
profile `f_u(v)=mu([uv])/mu([u])` therefore obeys

```text
C^-1 mu([v]) <= f_u(v) <= C mu([v])                     (QBP)
```

uniformly in the start word and its depth.

| Test | Result | Reason |
|---|---|---|
| S | PASS conditionally | `(QBP)` is uniform even when `|u|` escapes; it compares back to cylinders rooted at the original empty word. |
| P | FAIL on checked inputs | T14/T33/T37 rows are not proved to be conditional profiles of this one Gibbs measure with one constant `C`. |
| M | PASS conditionally | `(QBP)` transfers positive limiting tangent mass to positive original cylinder mass without requiring `inf_u mu([u]) > 0`. |
| B | PASS conditionally for the fixed-measure target only | A supplied tangent branch becomes a branch in `mu` with threshold loss. No stable changing-row conclusion follows. |

**First unmatched hypothesis: P, one fixed uniformly quasi-Bernoulli measure.**
Weak convergence of fixed-depth empirical cylinders does not imply `(QBP)` for
prefixes whose depths move with the row.

The exact conditional consequence is now specialized to the full finite shift,
so every concatenation is admissible. Suppose roots `u_q` satisfy
`mu([u_q])>0`, every `f_q(v)=mu([u_qv])/mu([u_q])` converges to `t(v)`, and a
separately supplied tangent branch with prefixes `p_i` satisfies

```text
t(p_i) > 0,       alpha*t(p_i) <= t(p_(i+1)).
```

Passing `(QBP)` to the limit gives

```text
C^-1 mu([v]) <= t(v) <= C mu([v]).
```

Hence `mu([p_i])>0`, and

```text
(alpha/C^2) * mu([p_i]) <= mu([p_(i+1)])               (PB)
```

for every `i`. This is an original-coordinate branch in the fixed reference
measure, but only under the additional single-measure premise and the supplied
tangent branch. It does not imply eventual inequalities in changing empirical
rows and gives no unconditional statement about the decimal orbit of pi.

### S3. Kaenmaki--Sahlsten--Shmerkin, Theorem 3.10: `DOES NOT APPLY`

The source considers normalized magnifications of one Radon measure at a fixed
spatial point, then time averages those sceneries. Theorem 3.10 says every
tangent distribution is a fractal distribution at almost every center.

| Test | Result | Reason |
|---|---|---|
| S | FAIL | Scale tends to infinity and coordinates are recentered at the spatial center; no absolute decimal-tree start is retained. |
| P | FAIL for T14/T37 | Quasi-Palm transports fixed full-measure scenery events, not row-dependent dominant-edge predicates. |
| M | PASS only in normalized scenery space | Sceneries are probabilities and tangent distributions form a compact nonempty set; original cylinder mass is not bounded below. |
| B | FAIL | The conclusion quantifies almost-every center and every tangent distribution, but contains no root/continuation branch. |

**First unmatched hypothesis/conclusion: S, start-depth anchoring.** There is
also a type mismatch before any application: T33 has individual coordinatewise
limits of arbitrary normalized count rows, not time-averaged Euclidean
sceneries of one Radon measure.

### S4. Almeida--Costa symbolic correspondence: `DOES NOT APPLY`

The cited correspondence identifies subshifts over one finite alphabet with
one fixed factorial, prolongable language. It validates an infinite symbolic
point when admissibility is fixed and shift-compatible.

| Test | Result | Reason |
|---|---|---|
| S | FAIL for pullback | Shift coordinates allow an occurrence to be moved to zero; an external absolute start is erased. |
| P | PASS only under one fixed language | T14/T37 row, cutoff, and threshold dependence do not define such a language. |
| M | FAIL | The result is purely topological and carries no positive cylinder mass or leakage estimate. |
| B | FAIL for the requested target | It produces a shift point, not a branch attached to one original absolute root. |

**First unmatched hypothesis/conclusion: S, start-depth anchoring.** Even after
adding an anchor, the first source hypothesis absent from T14 is one fixed
factorial/prolongable language. T29 already supplies the more general
level-dependent inverse-limit theorem once its explicit bounded-start,
fixed-predicate premise is assumed; importing this symbolic theorem would add
shift invariance without closing the T14 gap.

## 4. Applicability matrix against checked tracks

Each cell gives `verdict; first unmatched ordered test`. A conditional cell
names the extra premise immediately after the table.

| Source | T14 | T29 | T33 | T37 artificial stream only |
|---|---|---|---|---|
| Lyons--Peres 15.20 | DOES NOT APPLY; S | DOES NOT APPLY; S | DOES NOT APPLY; S | DOES NOT APPLY; S |
| Feng--Lau 1.1/(1.4) | DOES NOT APPLY; P | DOES NOT APPLY; P | CONDITIONAL; P | DOES NOT APPLY; P |
| KSS 3.10 | DOES NOT APPLY; S | DOES NOT APPLY; S | DOES NOT APPLY; S | DOES NOT APPLY; S |
| Almeida--Costa correspondence | DOES NOT APPLY; S | DOES NOT APPLY; S | DOES NOT APPLY; S | DOES NOT APPLY; S |

The sole Feng--Lau conditional cell requires that the T33 rows be conditional
cylinder laws of one fixed full-shift measure satisfying `(QB)` with one
constant. T33 already supplies the tangent branch and pointwise convergence;
under the additional representation, `(PB)` gives a fixed-measure original
branch. T14 supplies neither this representation nor a tangent branch, so
repairing P would still leave B unmatched. T29 already proves its branch from
its own hypotheses and has no Gibbs-measure interface to which Feng--Lau
applies. For the literal T37 rows no Feng--Lau matrix potential or uniform
quasi-Bernoulli representation is supplied, and `(PB)` would not imply T37's
stable changing-row quantifiers in any event.

For T29, Almeida--Costa remains `DOES NOT APPLY`: its shift point has no
distinguished absolute start or anchor-preserving decoder. Adding a fixed
factorial, prolongable language alone would not repair S. T29's own checked
inverse-limit theorem is both more general and already anchored by its bounded
start conclusion.

No retained source is marked `APPLIES`: none converts only the exact checked
T14/T33 hypotheses into the requested original-coordinate conclusion.

## 5. One formalization target

At most one target is retained:

```text
quasiBernoulli_tangentBranch_pullback
```

Formal statement shape: for a finite full shift, a cylinder mass `mu`,
constants `C >= 1` and `alpha > 0`, a root sequence `u_q`, and a tangent
profile `t`, assume `(QB)` for all words, `mu([u_q])>0`, pointwise convergence
`mu([u_q v])/mu([u_q]) -> t(v)`, and a supplied tangent branch `p_i` with
`p_0=[]`, `p_(i+1)=p_i++[digit_i]`, `t(p_i)>0`, and
`alpha*t(p_i)<=t(p_(i+1))`. Conclude for every `i`

```text
mu([p_i]) > 0
(alpha / C^2) * mu([p_i]) <= mu([p_(i+1)]).
```

This target formalizes only the four-line comparison leading to `(PB)` for one
fixed reference measure. It does not conclude stable inequalities in changing
rows. It must not postulate or conclude that pi's empirical rows satisfy
`(QB)`. T29's bounded-start compactness is not selected because it is already
machine-checked.

## 6. Final bounded conclusion

The audit is negative for generic compactness. Tree-derived limits, scenery
limits, and symbolic shift limits all permit recentering that loses the
absolute root. T29 already states the exact repair: bounded starts and one
fixed predicate. For the narrower fixed-measure target, uniform
quasi-Bernoulli comparison can replace bounded starts by quantitative
distortion control, but that premise is absent from T14, T33, and T37 and says
nothing by itself about stable changing empirical rows.

Therefore further generic tangent or compactness work cannot honestly claim a
pullback from the checked hypotheses. Any next step must establish either
T29's named synchronization premise or the explicit quasi-Bernoulli premise.
Nothing here establishes either premise for pi, C2, or canonical A1.
