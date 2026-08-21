# T27: collision leakage and coherent dominant paths

Status: `proof sketch` (the finite theorem below is proved in numbered prose,
not machine-checked).

## 1. Provenance and scope

- Canonical source: `knowledge/pi/statements/pi-lacunary-near-return-sparsity.txt`.
- Canonical source URL: none; this is a local problem formulated by the
  program.
- Canonical source SHA-256:
  `cbf56699b651aeb69301265763e38da44feb59c6fd955d2280887e8c06c6a2f8`.
- Hash rechecked: 2026-07-23.
- T27 studies an abstract finite base-10 count tree. It is an A14 sibling
  interface, not the canonical fixed-pi statement.

Nothing below proves or assumes C2, canonical A1, any unconditional property
of pi, or any block-occurrence claim. The imported mathematical facts used in
Section 8 are the exact types of the cited kernel-checked T9 and T14 Lean
declarations; the finite tree theorem and both examples are proved and
computed here.

## 2. Normalized statement and ambiguities

Let `A = {0,1,...,9}`. For a word `w`, write `|w|` for its length and `wa` for
the word obtained by appending digit `a`. Fix integers `0 <= r < s`. A finite
base-10 count tree of depth `s` is a family of nonnegative integers

```text
c_w,  w in A^j,  0 <= j <= s,
```

satisfying the conservation identity

```text
c_w = sum_{a in A} c_(wa)                    (C)
```

for every `|w| < s`. Assume `c_empty > 0`.

The following choices remove all relevant ambiguity.

1. Zero-count children are present, so every node has exactly ten children.
2. Collision energy uses ordered, diagonal-inclusive pairs, hence squares
   `c_w^2`, consistently with the canonical normalization.
3. The selected levels are the consecutive refinement levels
   `r,r+1,...,s-1`. Consecutiveness is a theorem hypothesis, not a conclusion.
4. At selected level `j`, fix `alpha_j` with `0 < alpha_j <= 1`. A positive
   node `w` is `alpha_j`-dominant if at least one child satisfies
   `c_(wa) >= alpha_j c_w`.
5. For every dominant node choose one such child, denoted `d_j(w)`. Ties may
   be broken by the least digit. All inequalities below hold for any such
   fixed choice.
6. Zero nodes are excluded from the dominant set. Including them changes no
   energy sum and no conclusion.
7. The theorem does not cover a nonconsecutive set of adjacent T14 levels:
   an additional transition rule across each omitted gap would be needed.

## 3. Conservation and collision energy

For every level `j`, define total mass and collision energy by

```text
N_j = sum_{|w|=j} c_w,
E_j = sum_{|w|=j} c_w^2.
```

The identities needed later are as follows.

1. Summing (C) over all words of length `j` gives

   ```text
   N_j = sum_{|w|=j} sum_a c_(wa) = N_(j+1).
   ```

   Therefore every `N_j` equals `c_empty > 0`.

2. For each parent, nonnegativity gives

   ```text
   sum_a c_(wa)^2 <= (sum_a c_(wa))^2 = c_w^2.
   ```

   Summing over parents gives the exact monotonicity

   ```text
   0 < E_(j+1) <= E_j.                        (1)
   ```

3. Positivity in (1) follows because the positive total mass forces at least
   one positive count at every level. Thus every normalization by `E_j` below
   is legitimate.

This is the same finite refinement identity represented in the kernel-checked
T9 declarations `piCylinderCollisionEnergy_succ_refinement` and
`piCylinderCollisionEnergy_succ_le`; the present proof is self-contained and
does not rely on prose from an earlier note.

## 4. Dominant-edge retention and normalized leakage

Let `G_j` be the set of positive `alpha_j`-dominant words at level `j`. Define

```text
D_j = sum_{w in G_j} c_w^2,
R_j = sum_{w in G_j} c_(w d_j(w))^2,
L_j = E_j - R_j,
rho_j = R_j / E_j,
ell_j = L_j / E_j = 1 - rho_j.                (2)
```

Here `D_j` is dominant-parent collision energy, `R_j` is the collision energy
retained by the chosen dominant edges, and `ell_j` is normalized full-edge
leakage. The word "full" matters: `L_j` charges both all energy on parents
outside `G_j` and all square-mass lost from a dominant parent to its nine
unchosen children. Explicitly,

```text
L_j = sum_{w in G_j} (c_w^2 - c_(w d_j(w))^2)
      + sum_{w notin G_j, |w|=j} c_w^2.       (3)
```

Every summand in (3) is nonnegative because a child count is at most its
parent count. Hence `0 <= ell_j <= 1`.

If for constants `0 <= mu_j < 1` one has

```text
D_j >= (1 - mu_j) E_j,                        (4)
```

then the definition of dominance gives

```text
R_j >= alpha_j^2 D_j
    >= alpha_j^2 (1 - mu_j) E_j.
```

Consequently every constant in the local leakage bound is explicit:

```text
ell_j <= delta_j,
delta_j = 1 - alpha_j^2 (1 - mu_j).           (5)
```

The square on `alpha_j` cannot be omitted because the energy is quadratic.

## 5. Quantitative coherent-path theorem

For the fixed choices above, recursively define the surviving coherent sets

```text
C_r = {w in A^r : c_w > 0},
C_(j+1) = {w d_j(w) : w in C_j intersect G_j}.
```

Let

```text
M_j = sum_{w in C_j} c_w^2,
K_r = |C_r|,
Q = E_r - sum_{j=r}^{s-1} L_j.                (6)
```

`K_r >= 1`. Every member of `C_s` is the endpoint of one genuinely nested
path whose edge at every selected level is the chosen dominant edge.

**Theorem (bounded full-edge leakage gives one coherent path).** For every
finite count tree and every choice above,

```text
M_s >= Q.                                      (7)
```

If `Q > 0`, then `C_s` is nonempty and some nested dominant path
`w_r < w_(r+1) < ... < w_s` satisfies the exact integer bound

```text
c_(w_s)^2 >= ceil(Q / K_r),
c_(w_s) >= isqrtceil(ceil(Q / K_r)),           (8)
```

where `isqrtceil(x)` is the least nonnegative integer `t` with `t^2 >= x`.
Every surviving path also satisfies

```text
c_(w_s) >= (product_{j=r}^{s-1} alpha_j) c_(w_r).   (9)
```

Equivalently, since `L_j = E_j ell_j`, if

```text
sum_{j=r}^{s-1} (E_j / E_r) ell_j <= Lambda < 1,   (10)
```

then (8) holds with `Q` replaced by `(1-Lambda)E_r`. The simpler but weaker
hypothesis `sum_j ell_j <= Lambda < 1` also suffices by (1).

### Proof in numbered steps

1. By definition, `M_r = E_r`.
2. Different parents have different children. Therefore

   ```text
   M_(j+1) = sum_{w in C_j intersect G_j} c_(w d_j(w))^2.
   ```

3. Subtracting this equality from `M_j` gives

   ```text
   M_j - M_(j+1)
     = sum_{w in C_j intersect G_j}
         (c_w^2 - c_(w d_j(w))^2)
       + sum_{w in C_j minus G_j} c_w^2.
   ```

4. All summands are nonnegative. Enlarging both sums from `C_j` to the full
   level and using (3) gives `M_j - M_(j+1) <= L_j`.
5. Sum Step 4 for `j=r,...,s-1`. The left side telescopes, so
   `E_r - M_s <= sum_j L_j`, which is exactly (7).
6. If `Q>0`, then (7) implies `M_s>0`, so `C_s` is nonempty.
7. Each starting word has at most one chosen continuation; hence
   `|C_s| <= K_r`. If every endpoint square were below `ceil(Q/K_r)`, their
   integer sum would be below `Q`, contradicting (7). This proves the first
   inequality in (8), and the definition of `isqrtceil` proves the second.
8. On a surviving edge, `c_(w d_j(w)) >= alpha_j c_w`. Multiplication down
   the nested path proves (9).
9. Substitute `L_j=E_j ell_j` into (6) to obtain (10). Finally, (1) gives
   `E_j/E_r <= 1`, proving the simpler sufficient condition.

This completes the numbered prose proof of the candidate theorem. Its
verification label remains `proof sketch`, not `machine-checked`.

## 6. Exact positive example: equality in the retained bound

All omitted children have count zero. Take `r=0`, `s=2` and

```text
c_empty = 12;
c_0 = 9, c_1 = 3;
c_00 = 8, c_01 = 1, c_10 = 3.
```

Choose `alpha_0=3/4`, `alpha_1=8/9`, and always choose the largest child.
The exact checks are:

1. Conservation: `12=9+3`, `9=8+1`, and `3=3`.
2. Energies: `E_0=12^2=144`, `E_1=9^2+3^2=90`, and
   `E_2=8^2+1^2+3^2=74`.
3. At level 0, `G_0={empty}`, `R_0=9^2=81`, so
   `L_0=144-81=63` and `ell_0=63/144=7/16`.
4. At level 1, both positive parents are dominant:
   `8=(8/9)9` and `3 >= (8/9)3`. Thus `R_1=8^2+3^2=73`,
   `L_1=90-73=17`, and `ell_1=17/90`.
5. The exact initial-energy leakage is
   `(L_0+L_1)/E_0=80/144=5/9<1`, and `Q=144-80=64`.
6. Here `K_0=1`. Formula (8) gives `c_(w_2)>=sqrt(64)=8`.
   The unique coherent path is `empty < 0 < 00`, and `c_00=8`, so (7) and
   (8) are equalities.
7. Formula (9) also gives
   `(3/4)(8/9)12=8`, again equality.

## 7. Exact counterexample: levelwise dominance migrates

This example shows that one fixed parameter tuple's strict levelwise
weighted-dominance conclusions do not by themselves imply `Q>0`, (10), or
even a two-edge dominant path. It does not refute the full T14 theorem, whose
failure conclusion is universal in the parameters; Section 8 uses that extra
quantifier. The example is an abstract count tree, not a claim that these
counts arise from the decimal orbit of pi.

Take `r=0`, `s=2` and set

```text
eta = 1/11,  alpha = 1 - 9 eta = 2/11,  mu = 9/10.
```

All omitted children have count zero. Define

```text
c_empty = 12;
c_0 = 6, and c_i = 1 for i=1,...,6;
c_(0a) = 1 for a=0,...,5;
c_(i0) = 1 for i=1,...,6.
```

The exact checks are:

1. Conservation: `12=6+6*1`, `6=6*1`, and each singleton satisfies `1=1`.
2. Energies: `E_0=12^2=144`, `E_1=6^2+6*1^2=42`, and
   `E_2=12*1^2=12`.
3. At the root, the split threshold is `eta*12=12/11`. Only child `0`, of
   count `6`, reaches it. Thus the root is not T9-quantitatively split. Its
   dominant threshold is `alpha*12=24/11`, reached only by child `0`.
4. Parent `0` has six children of count `1`. Since `1>=eta*6=6/11`, it is
   quantitatively split. But `1<alpha*6=12/11`, so it has no dominant child.
5. Each parent `i=1,...,6` has one child of count `1`. It is not split and is
   dominant because `1>=alpha*1=2/11`.
6. Level 0 is a nonsplitting level: its split-parent energy is `0`, strictly
   below `mu E_0=(9/10)144=648/5`.
7. Level 1 is also nonsplitting: its split-parent energy is `6^2=36`, while
   `mu E_1=(9/10)42=189/5`, and `36<189/5`.
8. Dominant-parent energies are `D_0=144` and `D_1=6`. The exact strict
   T14-style inequalities are

   ```text
   (1-mu)E_0 = 72/5 < 144 = D_0,
   (1-mu)E_1 = 21/5 < 6 = D_1.
   ```

9. Nevertheless, the root's only dominant edge goes to parent `0`, which has
   no dominant child. The dominant parents at level 1 are instead the six
   off-path singleton parents. Hence no nested two-edge dominant path exists.
10. The selected-edge retentions are `R_0=6^2=36` and `R_1=6*1^2=6`.
    Therefore

    ```text
    L_0=144-36=108, ell_0=3/4;
    L_1=42-6=36,    ell_1=6/7;
    ell_0+ell_1=45/28>1;
    (L_0+L_1)/E_0=144/144=1;
    Q=144-108-36=0.
    ```

The example hits the theorem's strict boundary exactly: replacing `Q>0` by
`Q>=0`, or replacing `Lambda<1` by `Lambda<=1`, would make the path conclusion
false. Thus those constants are sharp for this additive theorem.

## 8. Exact relation to the machine-checked T14 witness

This section uses only the checked theorem types in
`knowledge_library/t14/CoherentSuccessorSplitting.lean` and its checked T9
dependency, not any unverified prose-note conclusion.

1. T9 defines a parent as split when two distinct children each have count at
   least `eta c_w`. At a nonsplitting level, fewer than a `mu` fraction of
   collision energy lies on split parents.
2. T9's machine-checked
   `not_splitParent_hasDominantSuccessor` gives every nonsplit parent a child
   of count at least

   ```text
   alpha c_w,  alpha = 1 - 9 eta,
   ```

   under `0<eta<=1/10`. Hence `alpha>=1/10>0`.
3. T9's machine-checked
   `not_splittingLevel_dominant_energy_concentration` gives, strictly,

   ```text
   (1-mu) E_j < D_j                         (11)
   ```

   for each nonsplitting level, under `0<mu<1`.
4. T14's machine-checked theorem
   `not_piPolynomialSmallBallC2_implies_failure_and_weighted_dominance` is
   conditional on literal `not C2`. For every admissible fixed parameter tuple
   and candidate coherent prefix sequence, it produces one bad triangle entry
   `(k,m)` with

   ```text
   piSplittingLevelCount(m,N(k),mu,eta) < d*m-B,
   ```

   and supplies (11) separately for every nonsplitting `j<m`. T14 explicitly
   states: "No common or nested branch is claimed."
5. Choosing one qualifying child for every dominant parent and applying (11)
   to (5) gives the valid strict local consequence

   ```text
   ell_j < delta(mu,eta),
   delta(mu,eta) = 1-(1-mu)(1-9eta)^2
                 = mu+(1-mu)(18eta-81eta^2). (12)
   ```

6. The full universal parameter quantifier in T14 can force the hypotheses of
   Section 5. Fix any requested integer path length `h>=1`, and choose

   ```text
   mu_h = eta_h = 1/(100h),
   d_h = 1/(2h),  B=0,  m_0=2h.               (13)
   ```

   These parameters are admissible:
   `0<mu_h<1`, `0<eta_h<=1/100<=1/10`, and `d_h>0`.
7. Conditional on T14's premise `not C2`, and for any sequence `N` and limit
   `nu` satisfying the other hypotheses of its theorem, instantiate T14 with
   (13). It returns `k,m` with `m>=2h` and a splitting count `S` satisfying

   ```text
   S < m/(2h).                                  (14)
   ```

8. There must be `h` consecutive nonsplitting levels among `0,...,m-1`.
   Indeed, if there were no such run, each of the `floor(m/h)` disjoint full
   blocks of length `h` would contain a splitting level. Hence

   ```text
   S >= floor(m/h) >= m/h-1 >= m/(2h),
   ```

   where the last inequality is exactly `m>=2h`. This contradicts (14).
   Let the resulting run be `r,r+1,...,r+h-1`.
9. Put `x=1/(100h)` and `alpha_h=1-9x`. On every level of the run, (12) gives

   ```text
   ell_j < delta_h = 1-(1-x)(1-9x)^2.
   ```

   Expanding the retained factor gives

   ```text
   (1-x)(1-9x)^2 = 1-19x+99x^2-81x^3
                  >= 1-19x,
   ```

   because `x^2(99-81x)>=0`. Therefore

   ```text
   delta_h <= 19x = 19/(100h),
   sum_{j=r}^{r+h-1} ell_j < 19/100 < 1.       (15)
   ```

10. Apply Section 5 with `s=r+h` and `Lambda=19/100`. If `K_r` is the number
    of positive level-`r` cylinders and `E_r` their collision energy, one
    nested path of T14-dominant edges has terminal count satisfying

    ```text
    c_(w_(r+h))^2 >= ceil(81 E_r / (100 K_r)),
    c_(w_(r+h)) >= isqrtceil(ceil(81 E_r/(100 K_r))).  (16)
    ```

    Every edge also retains the factor `alpha_h=1-9/(100h)`, so the terminal
    count is at least `alpha_h^h c_(w_r)` along that path.
11. This implication uses T14's full universal quantification. The fixed
    `(mu,eta)` tree in Section 7 is consistent with (11), but it cannot model
    all parameter instantiations (13), so it is not a counterexample to Steps
    6-10. It instead proves that parameter tuning and the cumulative estimate
    are essential, rather than cosmetic.
12. The conclusion remains finite and nonuniform. The cutoff `N(k)`, row
    `m`, starting level `r`, and path may all depend on `h` and on the chosen
    coherent prefix sequence. Nothing here produces one infinite branch,
    compatibility between the paths for different `h`, C2, canonical A1, or
    an unconditional statement about pi. T25's cumulative quantity still
    counts independent row thresholds; equation (15) is the new pathwise
    bridge.

**Determination:** conditional on the literal `not C2` premise and the other
inputs of T14's checked failure theorem, T14 **does imply** T27's bounded
cumulative leakage hypothesis on some consecutive run of every prescribed
finite length `h`, with the explicit constants (13)-(16). A single fixed
parameter instance of T14's local weighted-dominance output does not suffice,
as Section 7 shows.

## 9. Reproduction and verification status

Run the example replay and artifact check from this artifact directory:

```sh
python3 -B verify_examples.py
sha256sum -c SHA256SUMS
```

Run the dependency check from the AllMath project root:

```sh
sha256sum -c \
  removed-workflow-record://todo-theory-pi-lacunary-near-return-sparsity-t27-1784838199-r0/theory_artifacts/DEPENDENCIES.sha256
```

The script uses Python integers and `fractions.Fraction`; it checks every
listed conservation equation, energy, splitting and dominance threshold,
strict weighted inequality, leakage value, theorem bound, and path verdict.
The computations verify the examples only. The universal theorem rests on the
numbered proof in Section 5 and remains a `proof sketch` until formalized.

## 10. Final verdict

Bounded cumulative full-edge leakage on consecutive selected levels yields a
single nested dominant path with the explicit retained-mass bounds (8)-(10).
The exact integer tree in Section 7 shows that fixed-parameter levelwise
dominance alone permits mass migration and reaches the additive threshold
`Q=0`. However, T14's full universally quantified conditional failure witness
does imply the finite leakage hypothesis after the parameter choice (13),
yielding the explicit bound (16). This is not a claim that C2 fails or an
unconditional claim about pi.

**PROVED**
