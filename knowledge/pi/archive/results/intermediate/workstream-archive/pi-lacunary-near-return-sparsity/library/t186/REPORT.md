# T186: explicit two-sided factor energy for d-bonacci words

Audit date: 2026-08-13 UTC. Source statements attributed to S1 and S2 are
`literature-checked` against the pinned PDFs and exact ranges in
`SOURCE_LEDGER.csv`. The derivation below is a `proof sketch`, not
machine-checked. T166 is used only at its kernel-checked generic finite-word
interface. The replay is an `experiment` checking pins, finite recurrences,
endpoints, constants, and sample energies; finite computation is not proof.

```text
RELATED_MODEL_VERDICT_COUNT: 1
FIXED_PI_CLAIM: none
A1_CLAIM: none
C1_CLAIM: none
C2_CLAIM: none
```

## 1. Scope, statement, and ambiguities

The byte-exact `canonical_statement.txt` has SHA-256
`cbf56699b651aeb69301265763e38da44feb59c6fd955d2280887e8c06c6a2f8`.
Its provenance records a local formulation on 2026-07-22 and no external
original-source URL. It asks about strict circle-distance near returns of the
fixed decimal orbit of pi, with ordered pairs and diagonal included.

T186 instead gives a `proof sketch` of a symbolic A13/A14 sibling statement
for one named family.
Fix an integer `d>=2`, the alphabet `A_d={0,...,d-1}`, and the morphism

```text
tau_d(a)=0(a+1) for 0<=a<d-1,       tau_d(d-1)=0.          (1.1)
```

The nested words `tau_d^q(0)` define the one-sided fixed point
`t^(d)=t_0t_1...`. S1 Example 3 states that this is the `d`-bonacci word and a
standard `d`-ary Arnoux--Rauzy word.

Normalized quantifiers and ambiguities:

1. `d>=2`, `m>=1`, and `N>=1` are integers; `d` is fixed before `m,N` vary.
2. The theorem below applies whenever `N>=2m`; thus `N_0(d)=2`.
3. `N` counts starts, not symbols in a truncated word. Symbols through index
   `N+m-2` are inspected.
4. Starts overlap without restriction; no cyclic wrapping is allowed.
5. Ordered pairs are counted and every diagonal pair is included.
6. Constants may depend on `d` but not jointly or separately on `m,N`.
7. This symbolic equality model is not substituted into the canonical metric
   question and has no proved transfer to it.

## 2. Exact observable and endpoint conventions

For `0<=i<N`, define the inclusive length-`m` factor

```text
B_d(i,m)=t_i t_(i+1) ... t_(i+m-1).                       (2.1)
```

The last legal start is `N-1`; its last read symbol is `N+m-2`. Start `N` is
illegal. For every word `u` of length `m`, define

```text
c_d(u;m,N)=#{i in {0,...,N-1}: B_d(i,m)=u},
E_d(m,N)=sum_u c_d(u;m,N)^2
        =#{(i,j) in {0,...,N-1}^2:B_d(i,m)=B_d(j,m)}.       (2.2)
```

The sum may equivalently range over observed factors because unobserved terms
are zero. Consequently

```text
sum_u c_d(u;m,N)=N,       E_d(m,N)>=N,                    (2.3)
```

and `E_d(m,N)-N` is the even ordered off-diagonal energy.

This agrees with T166 after taking a finite word of length `L=N+m-1`: its
kernel-checked `legalStartCount L m=L+1-m=N`, `factorAt`,
`factorMultiplicity`, and `collisionEnergy` have exactly (2.1)--(2.2),
including the final start and diagonal.
`T166FiniteWordPowerFree.lean` is vendored with SHA-256
`f1da6482ee8ad2b6c5341a1e0a8923a8e3bbc28d1f76d8e0845e7bab1d0e60a0`;
T186 adds no Lean declaration and does not relabel its source-specific prose
premises as machine-checked.

## 3. Source-pinned constants

Let `D_q^(d)` be the integer sequence

```text
D_q=2^q                         for 0<=q<=d-1,
D_q=sum_(h=1)^d D_(q-h)         for q>=d.                 (3.1)
```

S1 pp. 12--14 defines this sequence and Lemma 19 gives
`|tau_d^q(0)|=D_q`. We use the following deliberately conservative constants:

```text
Q_d = D_d,
r_d = 2 D_(2d+1),
P_d = 4 r_d * 2 * Q_d = 16 D_d D_(2d+1),
c_d = 1/(2(d-1)),
C_d = 2 P_d = 32 D_d D_(2d+1),
N_0(d)=2.                                                    (3.2)
```

All are explicit positive integers or rationals recursively computable from
`d`. There is no hidden limit, asymptotic constant, or joint `m,N` parameter.

## 4. Lower bound

S1 Definition 2 states that every `d`-ary Arnoux--Rauzy word has exactly

```text
p_d(m)=(d-1)m+1                                             (4.1)
```

distinct factors of length `m`; Example 3 identifies `t^(d)` as such a word.
At most `p_d(m)` multiplicities in (2.2) are nonzero. Cauchy--Schwarz gives

```text
N^2=(sum_u c_d(u;m,N))^2 <= p_d(m) E_d(m,N).               (4.2)
```

For `d>=2,m>=1`, `(d-1)m+1<=2(d-1)m`, so

```text
E_d(m,N) >= N^2/((d-1)m+1)
           >= c_d N^2/m,       c_d=1/(2(d-1)).             (4.3)
```

This holds for every `N>=1`; no recurrence claim is used.

## 5. Explicit bounded-power certificate

This section instantiates S2 Lemma 13 and Theorem 17 directly for (1.1), rather
than treating the T164 note's reconstruction as established.

### 5.1 Iterate-length ratio

The incidence matrix of `tau_d` is primitive: every `tau_d^d(b)` contains
every alphabet letter. Here is the exact elementary reason, needed again
below. For `0<=k<=d-1`, the word `tau_d^k(0)` contains `0,...,k` and ends in
`k`, by induction from (1.1). Also every `tau_d(b)` begins in `0`, so every
`tau_d^d(b)=tau_d^(d-1)(tau_d(b))` begins with the complete block
`tau_d^(d-1)(0)`, which contains all `d` letters. Put

```text
S_q=max_b |tau_d^q(b)|,       I_q=min_b |tau_d^q(b)|.      (5.1)
```

For `0<=q<d`, every image has length at least one and at most `2^q`, hence
`S_q<=2^q I_q<=D_d I_q`. For `q=d+k`, every letter occurs in
`tau_d^d(b)`, while `|tau_d^d(b)|<=D_d` (the maximum is attained at `b=0`).
Therefore

```text
|tau_d^(d+k)(b)| <= D_d max_a |tau_d^k(a)|,
|tau_d^(d+k)(b')| >= sum_a |tau_d^k(a)|
                    >= max_a |tau_d^k(a)|,
```

and `S_q<=Q_d I_q` for all `q`, with `Q_d=D_d`. This is the explicit constant
required in S2 Lemma 13.

### 5.2 Maximum supertile length versus recurrence radius

S1 Example 3 identifies the dominant letter as `0`, and Claim 12 states the
resulting length-two language explicitly:

```text
L_2(t^(d))={00} union {0a,a0:1<=a<=d-1}.                  (5.2)
```

First put `W_d=tau_d^(d+1)(0)`. It contains every pair in (5.2), with no
appeal to finite computation:

1. For `1<=a<=d-1`, the letter `a-1` occurs in `tau_d^d(0)`, so its image
   `tau_d(a-1)=0a` occurs in `W_d`.
2. The induction above says `tau_d^a(0)` ends in `a`. In the decomposition
   `tau_d^(a+1)(0)=tau_d^a(0)tau_d^a(1)`, the second block begins in `0`.
   Hence `a0` occurs in `tau_d^(a+1)(0)`, and therefore in `W_d`.
3. In particular `(d-1)0` occurs in `tau_d^d(0)`. Applying `tau_d` turns
   this source boundary into `tau_d(d-1)tau_d(0)=001`, so `00` occurs in
   `W_d`.

Now set `q=2d+1`. Since every `tau_d^d(b)` begins in `0`, the exact
composition identity

```text
tau_d^q(b)=tau_d^(d+1)(tau_d^d(b))                         (5.3)
```

shows that every level-`q` supertile begins with the complete block `W_d`.
Thus every level-`q` supertile contains every length-two factor.

Next distinguish the two constants. Formula (5) in S1 Lemma 19 gives, for
every letter `a`,

```text
|tau_d^q(a)|=sum_(j=1)^(d-a) D_(q-j) <= sum_(j=1)^d D_(q-j)=D_q,
```

with equality at `a=0`. Therefore

```text
M_d:=max_a |tau_d^q(a)|=D_(2d+1)                          (5.4)
```

is the **maximum supertile length**, not yet a recurrence radius.

Because `t^(d)=tau_d^q(t^(d))`, the fixed point is tiled consecutively by
level-`q` supertiles. Any factor of length `2M_d` contains a complete such
supertile: if it begins at a supertile boundary, it contains that block; if it
begins inside one, the remaining suffix has length at most `M_d-1`, leaving
at least `M_d+1` symbols and therefore the entire next supertile, whose length
is at most `M_d`. That contained supertile includes `W_d`, hence all of (5.2).
Consequently

```text
r_d:=2M_d=2D_(2d+1)                                      (5.5)
```

is a valid **length-two recurrence radius** in the precise sense used in S2
Theorem 17: every factor of length `r_d` contains every length-two factor.
No product inequality involving `D_d D_(d+1)` is used.

### 5.3 Power exclusion and equal-factor separation

S2 Theorem 17 and its displayed proof give, for a nonperiodic primitive
substitution fixed point,

```text
w^P is a factor only if w is empty, for P=4 r S(tau_d) Q. (5.6)
```

Here `S(tau_d)=2`; (3.2) therefore gives `P=P_d`. The fixed point is
nonperiodic because S1 gives its unbounded factor complexity (4.1), whereas an
eventually periodic word has bounded factor complexity.

Alternatively, this last overlap implication is exactly the hypothesis-to-
conclusion interface kernel-checked by T166. If two equal length-`m` factors
start at distinct positions with gap `g`, T166's
`equal_factors_start_separation`, applied to the finite prefix through both
factors, gives

```text
g >= floor(m/(P_d-1))+1 > m/P_d.                           (5.7)
```

No claim from the T164 note is a premise: S2 supplies (5.3), Sections 5.1--5.2
verify its constants for this family, and T166 supplies the generic endpoint
and overlap deduction.

## 6. Upper bound and uniform range

Fix a length-`m` factor `u`. Its occurrence starts among `0,...,N-1` are
pairwise separated by more than `m/P_d` by (5.7). Hence

```text
c_d(u;m,N) <= 1+(N-1)P_d/m <= 1+P_d N/m.                  (6.1)
```

This is also the real-valued weakening of T166's kernel-checked exact
`factorMultiplicity_le_packing`. Since `sum_u c_d(u;m,N)=N`,

```text
E_d(m,N)=sum_u c_d(u;m,N)^2
          <= (max_u c_d(u;m,N)) N
          <= N + P_d N^2/m.                               (6.2)
```

For the declared range `N>=N_0(d)m=2m`, one has `N<=N^2/(2m)`. Since
`P_d>=1`, (6.2) yields

```text
E_d(m,N) <= (P_d+1/2)N^2/m
           <= 2P_d N^2/m = C_d N^2/m.                    (6.3)
```

Combining (4.3) and (6.3) gives the explicit uniform `proof sketch`

```text
for every d>=2,m>=1,N>=2m,
  [1/(2(d-1))] N^2/m <= E_d(m,N)
                       <= [32 D_d D_(2d+1)] N^2/m.         (6.4)
```

Thus, at `proof sketch` level, the T184 `NR-ENERGY-MULTIPLICITY` gap closes for the source-pinned
`d`-bonacci family. The closure does not reverse `nrC`: the lower side uses
the exact source-pinned factor complexity and the upper side uses independent
bounded-power separation plus T166 packing.

## 7. Clause-complete nonduplication comparison

`COMPARISON_LEDGER.csv` records each agenda clause separately. The operative
boundaries are:

1. **T164:** the T164 note argues, unverified, for an effective generic
   primitive-substitution power certificate and illustrates Fibonacci and
   Thue--Morse. T186 neither imports that deduction nor claims generic novelty;
   it independently instantiates S2 for the entire `d`-bonacci family and adds
   the source-specific factor-complexity lower bound needed for two-sided
   energy.
2. **T166:** this is kernel-checked and supplies the exact legal-start,
   endpoint, multiplicity, ordered-energy identity, power-free separation, and
   upper packing interface. It does not prove that a `d`-bonacci prefix is
   `P_d`-power-free and supplies no linear-complexity lower bound. T186's new
   work is exactly those two source-specific premises and their uniform
   instantiation.
3. **T176:** its pinned sources and proof-sketch deductions concern a Cantor
   heavy fiber, one automatic repeated offset, and structured sums. It has no
   `d`-bonacci source, no bounded-power certificate for this family, and no
   two-sided all-`m,N` energy result. T186 does not reopen its search lanes.
4. **T184:** the note argues, unverified, from exact `nrC` to a sparse
   every-window lower floor and names missing multiplicity. T186 uses the same
   independently pinned S1 PDF but a different source clause, (4.1), plus S2
   and T166. The T186 proof sketch closes that named family-specific gap with a quadratic-scale
   lower bound and matching-order upper bound; no T184 proof-sketch deduction
   is imported.

No bounded result above is claimed globally novel in the literature. The
claim is only that the displayed clauses and constants form a checkable
closure relative to the named program artifacts.

## 8. Separate unproved transfer toward T7

`DBONACCI-TO-T7-T186` is a `conjecture`, not a premise or conclusion. To use
this mechanism toward T7 one would need a fixed `d>=2`, one constant `L>=1`,
and, uniformly over the unbounded depth/prefix family required by T7, a
carry-safe coding from each decimal factor at starts of the actual digit word
of pi to a `d`-bonacci factor of length between `m/L` and `Lm`, such that:

1. equality of decimal factors is carried to equality of coded factors;
2. symbolic start distances distort by at most the factor `L`;
3. every decimal collision fiber is covered with uniformly bounded coding
   multiplicity; and
4. the symbolic endpoint through `N+m-2` corresponds to a valid finite decimal
   prefix without cyclic wrapping or discarded boundary mass.

No pinned source supplies any such coding for pi. Even under it, a separate
proved symbolic-to-metric implication would be required because equal decimal
factors are weaker than all circle-distance near returns. Accordingly T186
makes no conclusion about T7 or the canonical question.

## 9. Endpoint

**RELATED-MODEL VERDICT (1/1): CLOSE THE D-BONACCI MULTIPLICITY GAP.**

Close only `NR-ENERGY-MULTIPLICITY` for the explicitly defined `d`-bonacci
family and the exact range/constants in (6.4). This is a related symbolic model
and makes no statement about fixed pi, A1, C1, or C2.

## 10. Artifact-only replay

From a directory containing only the delivered files, run

```text
python3 verify_t186.py > replay_output.txt
cmp replay_output.txt raw_output.txt
sha256sum -c SHA256SUMS
```

The replay verifies local pins, exact source anchors, the complete comparison
rows, recurrence constants over a bounded falsification range, legal endpoints,
sample ordered diagonal-inclusive energies, the single verdict marker, and the
four no-claim markers. These finite checks are an `experiment` only.
