# T75: window-local equality multiplicity load

Status: `machine-checked` for the public Lean theorems listed in Section 10;
`proof sketch` for the finite charging theorem in Section 5 and the two exact
families in Section 7. The proofs are given from the definitions and do not use
the unverified T67 note. Verdict: the charging reduction succeeds, while the
resulting fixed-pi local-load estimate remains an explicit open frontier.

No claim is made about C7, C2, C1, positive factor entropy, or an asymptotic
property of the digits of pi.

## 1. Provenance and normalized scope

The canonical problem file is `pi-positive-decimal-factor-entropy.txt`. It was
formulated locally, so no original source URL exists to preserve. Its byte-exact
SHA-256 is

```text
a70dd741b27595aeb3dfc902b5e201579fed6bae24e2191f58c5ac64a22939e6
```

The canonical question asks whether one fixed `eta>0` gives
`p_pi(n)>=10^(eta*n)` for all sufficiently large `n`. T75 does not answer that
question. It studies a finite arbitrary-label statistic attached to the short
lag sector of the conditional sparse-collision route.

For every natural `n`, put

```text
L = L_n = 10^(n/2),
```

where `/` is natural-number division. Labels are an arbitrary function

```text
x : {0,...,L-1} -> {0,...,10^n-1}.
```

The pi specialization, when explicitly named, is T69's `piLabelSequence n`.
Every theorem before that specialization is about arbitrary finite labels.

### Ambiguities fixed

1. T56 short lags satisfy all three strict inequalities `0<r`, `r<n`, and
   `r<L`.
2. The maximum short lag is `h=min(n-1,L-1)`. If `h=0`, the short sector and
   all T75 windows are empty.
3. A window has nominal length exactly `2h`, is half-open, and is clipped at
   the ambient endpoints.
4. Window multiplicity counts positions, not lag incidences.
5. `m(m-1)` counts ordered distinct equal-label pairs. Diagonals are not in
   `A_loc`.
6. A pair may occur in two windows. This bounded duplication is intentional.
7. `A_loc` is defined without reference to `W5`, near returns, an arithmetic
   residual mask, or pi.
8. The two separating families are synthetic decimal-label families. They are
   not computed prefixes of pi and supply no fixed-pi evidence.

## 2. Exact imported conventions

The delivered Lean file imports
`TheoryLib.PiPositiveDecimalFactorEntropy.T69T69FiveCaseCharging`, which in
turn imports T56. The pinned source hashes are

```text
41e8ec69c4a113592b8f1de1dc5e02e815726c5a7e541ac7fd57afc6b181f1cc  T56T56LagSectorAudit.lean
43693adcb8678fd71c1ba866d91a025066b08a307a92ace165127dab1abcf3d9  T69T69FiveCaseCharging.lean
```

The following imported facts are kernel-checked.

1. `t56SampleLength n = 10^(n/2)`.
2. `mem_W5_lags_iff` says

   ```text
   r in shortResidualLags(n,L) iff 0<r and r<n and r<L.       (2.1)
   ```

3. T69 defines

   ```text
   W5(n,x) = 2 * sum_(r in shortResidualLags(n,L))
                    |adjacentStarts(n,x,r)|.                  (2.2)
   ```

   The factor two restores the reverse orientation. The start range is
   exactly `0<=j<L-r`.
4. `CyclicAdjacent(q,a,b)` is exactly equality, ordinary predecessor,
   ordinary successor, wrap predecessor, or wrap successor. T69 collapses
   these five endpoint cases to the identity, cyclic rotation, and inverse
   cyclic rotation permutations of `Fin q`.
5. `shortResidualPairCount_le_W5` says, for every `mu,c,Q0,n`,

   ```text
   shortResidualPairCount(mu,c,Q0,n,L)
      <= W5(n,piLabelSequence(n)).                            (2.3)
   ```

No T69 global `E3` estimate is assumed. No claim from the T67 note is used.

The T75 theorem `mem_shortLags_iff` rechecks from (2.1) that

```text
r in shortResidualLags(n,L) iff 0<r and r<=h.                (2.4)
```

This handles both strict upper endpoints without assuming `n<=L`.

## 3. Deterministic windows and bounded overlap

Suppose first that `h>0`. For every `0<=k<L`, define

```text
I_k = {i: 0<=i<L and
          floor(i/h)=k or floor(i/h)=k+1}.                   (3.1)
```

Equivalently,

```text
I_k = [k*h,(k+2)*h) intersect [0,L).                        (3.2)
```

Thus each untruncated window has length exactly twice the maximum T56 short
lag. Indices `k` after the final nonempty quotient block merely give empty
windows; retaining the deterministic range `0<=k<L` avoids ceiling conventions
and does not change any sum. For `h=0`, set every `I_k` to empty.

### 3.1 Pair cover

Let `0<=i<j<L` and `j-i<=h`. Put `k=floor(i/h)`. Euclidean division gives

```text
floor(i/h) <= floor(j/h) <= floor((i+h)/h)
             = floor(i/h)+1.                                (3.3)
```

Therefore both quotient blocks are `k` or `k+1`, and `i,j in I_k`. By (2.4),
every T56 short pair has this property. The Lean theorem
`pair_mem_localWindow` checks (3.3), including the equality case `j-i=h`.

### 3.2 Overlap two

Fix a position `i` and write `b=floor(i/h)`. From (3.1), `i in I_k` implies

```text
k=b or k=b-1.                                               (3.4)
```

Hence each position belongs to at most two windows. Double-counting incidences
`(k,i)` gives

```text
sum_(0<=k<L) |I_k| <= 2L.                                   (3.5)
```

The Lean theorems `containingWindows_card_le_two` and
`sum_localWindow_card_le_two_mul` check (3.4) and (3.5). This is a direct
proof; no component assertion from T67 is imported.

## 4. Definition of the local load

For a label `a` and window `I_k`, define

```text
m_k(a) = |{i in I_k : x(i)=a}|.                             (4.1)
```

The window-local equality multiplicity load is

```text
A_loc(n,x) = sum_(0<=k<L) sum_(0<=a<10^n)
               m_k(a)*(m_k(a)-1).                          (4.2)
```

In the Lean file the generic statistic is `ALoc x h`, and the named T56-scale
specialization is `t75ALoc n x = ALoc x (maxShortLag n)`. The generic
definition also permits other finite `L,q,h` so its combinatorics can be
reused. It depends only on deterministic windows and exact label equality. In
particular, it is independent of `W5`.

The identity

```text
sum_a m_k(a)=|I_k|                                          (4.3)
```

is checked by `sum_windowMultiplicity_eq_card`.

## 5. Charging theorem with explicit constants

For every natural `n` and every label sequence `x`,

```text
W5(n,x) <= 6L + 3*A_loc(n,x).                               (5.1)
```

Combining (2.3) and (5.1) gives, with no arithmetic assumption,

```text
shortResidualPairCount(mu,c,Q0,n,L)
  <= W5(n,piLabelSequence(n))
  <= 6L + 3*A_loc(n,piLabelSequence(n)).                    (5.2)
```

Thus one valid explicit choice of constants is

```text
C_0=6,  C_1=3.                                              (5.3)
```

Here is the complete finite proof of (5.1).

### 5.1 Every W5 incidence enters a local code graph

By (2.2), an upper-triangular W5 incidence is a pair `(i,j)=(s,s+r)` with
`0<r<=h`, `0<=s<L-r`, and cyclically adjacent labels. The factor two in W5
counts both orientations. Section 3.1 places both endpoints in at least one
window `I_k`.

Let `e_0` be the identity permutation of the `10^n` labels, `e_+` cyclic
successor, and `e_-` cyclic predecessor. For each window define

```text
G_(k,e) = {(u,v) in I_k x I_k : x(v)=e(x(u))}.               (5.4)
```

T69's checked five-to-three endpoint classification says every cyclically
adjacent ordered pair lies in one of `G_(k,e_0)`, `G_(k,e_+)`, or
`G_(k,e_-)`. The sets may overlap in small moduli and a pair may be covered by
two windows, but the union bound only overcounts. Therefore

```text
W5(n,x) <= sum_k sum_(e in {e_0,e_+,e_-}) |G_(k,e)|.        (5.5)
```

This step retains the wrap cases. It does not replace cyclic adjacency by
literal equality.

### 5.2 One permutation graph costs one local square load

Fix `k` and a permutation `e`. Partition (5.4) by the source label `a`:

```text
|G_(k,e)| = sum_a m_k(a)*m_k(e(a)).                         (5.6)
```

Finite Cauchy-Schwarz and permutation invariance give

```text
sum_a m_k(a)*m_k(e(a))
 <= sqrt(sum_a m_k(a)^2)*sqrt(sum_a m_k(e(a))^2)
 =  sum_a m_k(a)^2.                                        (5.7)
```

This is the same elementary finite argument that T69 checks globally, but it
has been reapplied here to each restricted window rather than treating the
global load as local. Using (4.3),

```text
sum_a m_k(a)^2
 = sum_a [m_k(a)*(m_k(a)-1)+m_k(a)]
 = A_k+|I_k|,                                              (5.8)
```

where `A_k` is the `k`th summand of (4.2).

### 5.3 Sum the three graphs and all windows

Equations (5.5)-(5.8) and (3.5) give

```text
W5(n,x)
 <= 3*sum_k (A_k+|I_k|)
 =  3*A_loc(n,x)+3*sum_k |I_k|
 <= 3*A_loc(n,x)+6L.                                      (5.9)
```

This proves (5.1) with no hidden onset and no asymptotic notation. If `h=0`,
the T56 short-lag set and all windows are empty, so both sides before `6L` are
zero and the same inequality holds.

## 6. Quantitative local-component inverse theorem

Let `K` be any natural number. If every label occurs at most `K` times in
every window, then

```text
m_k(a)*(m_k(a)-1) <= K*m_k(a).                              (6.1)
```

Summing (6.1), then using (4.3) and (3.5), gives

```text
A_loc(n,x) <= K*sum_k |I_k| <= 2*K*L.                      (6.2)
```

The contrapositive is the explicit inverse theorem

```text
2*K*L < A_loc(n,x)
  implies there exist k,a with m_k(a)>K.                    (6.3)
```

Both (6.2) and (6.3) are machine-checked respectively as
`ALoc_le_two_mul_of_multiplicity_le` and
`exists_local_component_gt_of_two_mul_lt_ALoc`.

Consequently, for any sequence of finite label systems with
`A_loc/L -> infinity`, the largest repeated equal-label component inside one
window tends to infinity: for each fixed `K`, eventually (6.3) applies. This
is a local equality component, not an overlap-periodicity component. No
Fine-Wilf, suffix, span, or T67 component claim is needed.

## 7. Two strict separating families

These are exact synthetic decimal-label families at the T56 scales. They are
not samples of pi.

### 7.1 Constant labels: local A_loc versus global E3

For every `n>=2`, let

```text
x_const(i)=0 for 0<=i<L.                                   (7.1)
```

T69's global equality load has one fiber of size `L`, hence

```text
equalityComponentLoad(x_const)=L^2,
E3(n,x_const)=3L^2.                                        (7.2)
```

For T75's windows put

```text
ell_k = min(2h, L-k*h),                                    (7.3)
```

where natural subtraction makes `ell_k=0` once `k*h>=L`.
Equations (3.1)-(3.2) show exactly that `|I_k|=ell_k`. There is one nonempty
label fiber in each window, so

```text
A_loc(n,x_const)
 = sum_(k=0)^(L-1) ell_k*(ell_k-1).                        (7.4)
```

Since `ell_k<=2h`, equations (3.5) and (7.4) give the explicit bound

```text
A_loc(n,x_const)
 <= 2h*sum_k ell_k
 <= 4hL.                                                   (7.5)
```

At even scales `n=2m`, `L=10^m` and `h=2m-1`. Therefore

```text
E3(n,x_const) / A_loc(n,x_const)
 >= 3L/(4h) = 3*10^m/(4*(2m-1)),                           (7.6)
```

and the right side is arbitrarily large. Thus T69's global `E3` can exceed
the local load by any prescribed factor. The exact formula (7.4), not a finite
experiment, defines the family at every scale.

### 7.2 Injective labels: A_loc is not W5 renamed

For every `n>=2`, `L<10^n`. Define

```text
x_inj(i)=i for 0<=i<L, regarded as a label below 10^n.      (7.7)
```

Every local label multiplicity is zero or one, hence

```text
A_loc(n,x_inj)=0.                                          (7.8)
```

This is also checked generically by `ALoc_eq_zero_of_injective`.

For an upper pair `(i,i+r)`, both labels lie in `[0,L)` and there is no wrap
at modulus `10^n`. They are cyclically adjacent exactly when `r=1`. Lag one
belongs to the strict T56 short range for every `n>=2`, and it has exactly
`L-1` starts. Therefore the definition (2.2) gives

```text
W5(n,x_inj)=2*(L-1)>0.                                     (7.9)
```

Equations (7.8)-(7.9) strictly separate the two statistics at arbitrarily
large scales and show why the additive `6L` term in (5.1) cannot simply be
deleted. `A_loc` is not `W5` under another name.

## 8. The fixed-pi frontier and nonclaims

The Lean file defines, only as an unproved predicate,

```text
PiALocLinearBound :<=>
  there exist K,N such that for every n>=N,
  A_loc(n,piLabelSequence(n)) <= K*L_n.                     (8.1)
```

If (8.1) were supplied, (5.2) would give the short-sector bound

```text
shortResidualPairCount(mu,c,Q0,n,L_n)
 <= (6+3K)*L_n.                                            (8.2)
```

T75 does not assert (8.1). No finite computation in the replay concerns pi,
and no synthetic-family observation is evidence for (8.1). This artifact
makes no C7, C2, C1, positive-entropy, normality, or disjunctivity claim. It
also makes no claim about the separate long residual sector or effective
irrationality hypotheses.

The honest outcome is therefore a successful reduction: global `E3` is
replaced by a genuinely local equality-cluster frontier, but that frontier is
still open for the fixed decimal orbit of pi.

## 9. Literature and library search log

On 2026-08-02 the local TheoryLib and pinned knowledge library were searched
for T56 short-sector definitions, T69's five-case classifier and code-graph
bound, window-cover lemmas, and local multiplicity inverses. T56 and T69 were
reused rather than redeclared. No existing T75-style bounded-overlap local
load theorem was found. T67 was found only under `notes/` and is an unverified
sketch, so no assertion from it is used. The argument is elementary finite
counting and makes no novelty claim; no external research citation is needed.

## 10. Machine-checked theorem map

All declarations are in the fresh namespace
`DecimalFactorComplexity.T75WindowLocalLoad`. The public reusable theorems are

```text
sampleLength_eq
mem_shortLags_iff
pair_mem_localWindow
containingWindows_card_le_two
sum_localWindow_card_le_two_mul
t75ALoc_eq
piALocLinearBound_iff_quantifiers
sum_windowMultiplicity_eq_card
ALoc_le_two_mul_of_multiplicity_le
exists_local_component_gt_of_two_mul_lt_ALoc
ALoc_eq_zero_of_injective
```

The Lean file contains no `sorry`, `admit`, `native_decide`, new axiom, unsafe
declaration, or opaque proof shortcut. Its printed axiom sets are subsets of
`propext`, `Classical.choice`, and `Quot.sound`.

## 11. Replay

From a directory containing only the delivered artifacts, run

```sh
sh ./verify.sh
```

The replay checks all pinned hashes and exact finite definitions. It verifies
the window membership formula, pair cover, overlap two, both sides of the
charging inequality, inverse thresholds, and both separating-family formulas
over declared synthetic ranges. These checks are `experiment`; the universal
claims rest on the proof above and the listed kernel-checked theorems. The
replay never reads or computes a digit of pi.
