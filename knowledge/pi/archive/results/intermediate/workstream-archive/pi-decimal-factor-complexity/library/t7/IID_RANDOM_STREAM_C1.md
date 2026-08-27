# T7: The exact C1 analogue for an iid uniform decimal stream

Claim status: **proof sketch** (a complete paper proof, awaiting independent
review).

This is a **generic random-stream sibling result**. It concerns a random
sequence of independent uniform decimal digits. It is not a statement about
the decimal expansion of pi. In particular, this artifact does not assert C1
for pi, canonical A1 for pi, normality or disjunctivity of pi, or any conclusion
about pi from finite computation.

## Source, scope, and reused definition

- Canonical statement: `knowledge/pi/statements/pi-decimal-factor-complexity.txt`
- Verified SHA-256:
  `e2b6c9375936a97fe6cdd10c3f014613267f3c491935b536c6ec016c5f501e43`
- Original source URL: none is recorded; this is a local problem statement.
- Agenda item: T7, serving G6.
- Reused accepted artifact:
  `knowledge_library/t4/FinitePrefixCollisionEnergy.lean`, SHA-256
  `805c1473696d94c689ea45f33d1c7270084518ebe20e5d3a05cbe094e485ceb1`.

T4 uses zero-based starts `0,...,N-1`, corresponding to decimal positions
`d_1,...,d_N`, and permits a sampled factor to extend beyond the last sampled
start. We use exactly that convention.

## Normalized statement

Let `D={0,1,...,9}`. There is a probability space carrying a random stream
`X=(X_0,X_1,...)` whose coordinates are independent and uniform on `D`. For
integers `n>=1`, `N>=1`, and `v in D^n`, define

```text
W_(n,i)(X) = (X_i,X_(i+1),...,X_(i+n-1)),
m_X(n,N;v) = |{i : 0 <= i < N and W_(n,i)(X)=v}|,
E_X(n,N)   = sum_(v in D^n) m_X(n,N;v)^2.
```

The unobserved terms in the last sum are zero, so this equals T4's sum over
observed factors. It includes diagonal ordered collision pairs.

Set

```text
N_n = 10^floor(n/3).
```

We prove the following exact almost-sure assertion.

**Theorem (iid sibling C1).** There is a measurable set `G` with `P(G)=1`
such that, for every `x in G`:

1. there is an integer `n_*(x)>=1` such that for every `n>=n_*(x)`, the
   windows `W_(n,0)(x),...,W_(n,N_n-1)(x)` are pairwise distinct and hence
   `E_x(n,N_n)=N_n`;
2. for every real `C>0`, there is an integer `n_0=n_0(x,C)>=1` such that for
   every integer `n>=n_0`, the particular choice `N=N_n>=1` satisfies

   ```text
   C n E_x(n,N) < N^2.
   ```

Thus the exact quantifier order is

```text
P({x : forall real C>0, exists n_0>=1, forall n>=n_0,
          exists N>=1, C*n*E_x(n,N) < N^2}) = 1.
```

The measurability of the displayed event is checked explicitly below rather
than inferred from an uncountable intersection. The witness `N` may depend on
`n`; here it is always the deterministic `N_n`.

## Probability space and source pin

Give `D` its discrete sigma-algebra and the uniform probability measure

```text
u(A)=|A|/10  for A subset D.
```

Here is a direct verification that `u` is a probability measure, as required
by the product-measure theorem below. Clearly `u(empty)=0` and
`u(D)=10/10=1`. If `(S_j)` is a countable pairwise-disjoint family of subsets
of `D`, at most ten of the `S_j` are nonempty. Cardinality is additive on
those finitely many disjoint sets, so

```text
u(union_j S_j)=|union_j S_j|/10
                =sum_j |S_j|/10
                =sum_j u(S_j).
```

Thus `u` is countably additive and has total mass one.

Take

```text
Omega = D^N,
F     = the product sigma-algebra,
P     = tensor_(t in N) u.
```

The coordinate map is `X_t(x)=x(t)`. Coordinate maps are measurable by the
definition of the product sigma-algebra. More generally, for a finite set `I`
of coordinates and arbitrary subsets `S_t subset D`, the finite-cylinder
formula is

```text
P({x : x(t) in S_t for every t in I})
  = product_(t in I) u(S_t)
  = product_(t in I) |S_t|/10.                      (1a)
```

Taking `I={t}` proves that `X_t` is uniform. Formula (1a), for every finite
`I` and every choice of the sets `S_t`, is exactly finite-coordinate
independence. In particular, for an assignment `a in D^I`, take
`S_t={a(t)}` to obtain

```text
P({x : x(t)=a(t) for every t in I})
  = product_(t in I) u({a(t)})
  = 10^(-|I|).                                      (1b)
```

Existence of this product probability measure and formula (1a) are
source-pinned to mathlib4 commit
`c5ea00351c28e24afc9f0f84379aa41082b1188f`:

- `Mathlib/Probability/ProductMeasure.lean`, SHA-256
  `a7ac088d987d154bcf8c2ff8a6cef943287e0437233457b3744f99c00dc6b961`;
- immutable URL:
  <https://github.com/leanprover-community/mathlib4/blob/c5ea00351c28e24afc9f0f84379aa41082b1188f/Mathlib/Probability/ProductMeasure.lean#L348-L404>;
- `Measure.infinitePi` is defined at lines 348--359, is proved to be a
  probability measure at lines 378--381, and `Measure.infinitePi_pi` gives the
  finite-cylinder product formula at lines 402--404.

This pin is used only for the standard product-measure construction and its
finite-cylinder values. Each fixed collision event `Q_(n,i,j)`, each `A_n`,
and each fixed-parameter energy inequality below depends on finitely many
coordinates. It is therefore measurable in the product sigma-algebra by
finite unions of measurable cylinders, and (1b) gives each cylinder's
probability. The tail events are countable unions and intersections of these;
their measurability is checked when they are introduced.

### Elementary measure facts used below

To avoid invoking any further probability theorem as a black box, we record
the measure consequences used later. They follow directly from countable
additivity and nonnegativity.

1. **Monotonicity.** If `A subset B`, then `B` is the disjoint union of `A`
   and `B\A`, so `P(B)=P(A)+P(B\A)>=P(A)`.
2. **Disjoint finite additivity.** If `A_1,...,A_m` are disjoint, countable
   additivity applied after setting all later sets to `empty` gives
   `P(union_r A_r)=sum_r P(A_r)`.
3. **Countable union bound.** For any events `(A_r)`, put
   `C_r=A_r\union_(s<r) A_s`. The `C_r` are disjoint, have the same union as
   the `A_r`, and satisfy `C_r subset A_r`. Countable additivity and
   monotonicity therefore give

   ```text
   P(union_r A_r)=sum_r P(C_r)<=sum_r P(A_r).
   ```

   The finite union bound is the special case obtained by appending empty
   events.
4. **Complements of null events.** Since `Omega=A` disjoint-union `A^c`,
   `1=P(Omega)=P(A)+P(A^c)`. Hence `P(A)=0` implies `P(A^c)=1`.

For comparison with a formal implementation, monotonicity is
`MeasureTheory.measure_mono` and the countable union bound is
`MeasureTheory.measure_iUnion_le` in the second source pin below. The direct
arguments above are all that is used in this artifact.

## Lemma 1: two windows collide with probability exactly `10^(-n)`

Fix `n>=1` and distinct starts `i,j`. By symmetry suppose `i<j`, and put
`d=j-i>=1`. Let

```text
Q_(n,i,j) = {x : W_(n,i)(x)=W_(n,j)(x)}.
```

We count assignments to precisely the coordinates occurring in the two
windows.

### Nonoverlapping case: `d>=n`

The two coordinate intervals are disjoint and contain `2n` coordinates.
There are `10^n` assignments satisfying equality: choose the `n` digits of
the first window arbitrarily, after which the second window is forced to be
the same word. By (1b), each assignment has probability `10^(-2n)`, and the
corresponding cylinder events are disjoint. Therefore

```text
P(Q_(n,i,j)) = 10^n * 10^(-2n) = 10^(-n).           (2)
```

This includes the adjacent case `d=n`.

### Overlapping case: `1<=d<n`

The union of the coordinate intervals is the integer interval
`[i,i+n+d)`, of cardinality `n+d`. Equality of the windows is exactly the
system

```text
x_(i+t)=x_(i+d+t)  for t=0,1,...,n-1.               (3)
```

There are exactly `10^d` assignments satisfying (3). Indeed, the first `d`
digits `x_i,...,x_(i+d-1)` may be chosen freely. Every later digit in the
union has index `i+q` with `d<=q<n+d`, and (3) with `t=q-d` forces it to equal
`x_(i+q-d)`, which was determined earlier. Conversely, this recursion gives
an assignment satisfying every equality in (3). Thus (1b), again over a
disjoint union of assignment cylinders, gives

```text
P(Q_(n,i,j)) = 10^d * 10^(-(n+d)) = 10^(-n).        (4)
```

Equations (2) and (4) prove, without assuming independence of overlapping
windows,

```text
P(W_(n,i)=W_(n,j)) = 10^(-n) for every i != j.      (5)
```

## Lemma 2: the bad-event probabilities are summable

Let

```text
A_n = {x : there exist 0<=i<j<N_n with W_(n,i)(x)=W_(n,j)(x)}.
```

There are `binom(N_n,2)` unordered pairs. Applying elementary measure fact 3
to this finite family and then using (5) gives

```text
P(A_n) <= binom(N_n,2) 10^(-n)
       <= N_n^2 10^(-n).                            (6)
```

Write `n=3k+r`, where `k=floor(n/3)` and `r in {0,1,2}`. Then `N_n=10^k`
and

```text
N_n^2 10^(-n) = 10^(2k-3k-r) = 10^(-k-r) <= 10^(-k).  (7)
```

The values `n>=1` form a subset of the triples `(k,r)` with `k>=0` and
`r in {0,1,2}`. Hence (6)--(7) imply the explicit convergent majorant

```text
sum_(n=1)^infinity P(A_n)
  <= 3 sum_(k=0)^infinity 10^(-k)
  = 3/(1-1/10)
  = 10/3 < infinity.                                (8)
```

No independence among the events `A_n` is asserted or needed.

## Lemma 3: the first Borel--Cantelli implication

For completeness, here is the exact part of Borel--Cantelli used in the
proof.

**First Borel--Cantelli lemma.** If events `(B_n)_(n>=1)` in a probability
space satisfy `sum_n P(B_n)<infinity`, then with probability one only finitely
many `B_n` occur.

**Proof.** For `m>=1`, let

```text
T_m = union_(n>=m) B_n,
L   = intersection_(m>=1) T_m.
```

Thus `L` is exactly the event that infinitely many `B_n` occur. Elementary
measure fact 3 gives

```text
P(T_m) <= sum_(n>=m) P(B_n).                         (9)
```

Because the nonnegative series converges, the Cauchy criterion for its partial
sums says that its tails tend to zero. Since `L subset T_m` for every `m`,
elementary measure fact 1 and (9) give

```text
0 <= P(L) <= P(T_m) <= sum_(n>=m) P(B_n).
```

For every `epsilon>0`, a sufficiently large `m` makes the last expression
smaller than `epsilon`; therefore `P(L)=0`. Its complement has probability
one, and membership in that complement means that there is an `m` after
which no `B_n` occurs. This proves the lemma. `square`

For an inspectable formal source for the countable-subadditivity inequality
used in (9), see theorem `MeasureTheory.measure_iUnion_le` at lines 69--75 of
mathlib4's
`Mathlib/MeasureTheory/OuterMeasure/Basic.lean`, at the same pinned commit:

- SHA-256:
  `9e739a4d20704494cc92d11be380512d956500fbc365b2eb3a9221f41a724fc1`;
- immutable URL:
  <https://github.com/leanprover-community/mathlib4/blob/c5ea00351c28e24afc9f0f84379aa41082b1188f/Mathlib/MeasureTheory/OuterMeasure/Basic.lean#L69-L75>.

Thus the Borel--Cantelli conclusion itself has been proved here rather than
invoked as a black box.

## Eventual collision-free prefixes

Apply Lemma 3 to `B_n=A_n` using (8). The event

```text
G = {x : there exists n_*(x)>=1 such that
         for every n>=n_*(x), x is not in A_n}
  = union_(m>=1) intersection_(n>=m) (Omega \ A_n)
```

is measurable because every `A_n` is measurable and sigma-algebras are closed
under complements and countable unions and intersections. Lemma 3 says its
complement is the null limsup event, so elementary measure fact 4 gives
`P(G)=1`. Fix `x in G` and a
corresponding `n_*(x)`. For each
`n>=n_*(x)`, not being in `A_n` says line by line that no pair
`0<=i<j<N_n` has equal windows. Therefore the `N_n` sampled windows are
pairwise distinct.

For such an `n`, exactly `N_n` words have nonzero multiplicity, and every one
of those multiplicities is `1`. Consequently

```text
E_x(n,N_n)
  = sum_(v in D^n) m_x(n,N_n;v)^2
  = N_n * 1^2
  = N_n.                                             (10)
```

This is also the ordered-collision interpretation from T4: only the `N_n`
diagonal pairs `(i,i)` remain.

## Growth of `N_n/n`

We prove the needed divergence without appealing to asymptotic notation.
First,

```text
10^k >= k^2 for every integer k>=1.                 (11)
```

The case `k=1` is immediate. If (11) holds at `k>=1`, then
`10^(k+1)>=10k^2>=(k+1)^2`, because
`10k^2-(k+1)^2=9k^2-2k-1>=6>0`.

Now write `n=3k+r` as above. For `k>=1`, equations (11) and
`3k+r<=3k+2<=5k` give

```text
N_n/n = 10^k/(3k+r) >= k^2/(5k) = k/5.             (12)
```

Given any real `C>0`, choose an integer `K>=1` with `K/5>C`. For every
`n>=3K`, its quotient `k=floor(n/3)` satisfies `k>=K`; hence (12) gives

```text
N_n/n > C, equivalently C*n < N_n.                  (13)
```

This proves `N_n/n -> infinity` in the full
`forall C, eventually-forall n` sense.

## Exact C1 deduction and quantifier audit

Fix the single measure-one set `G` above and any `x in G`. Now let an
arbitrary real `C>0` be given. Choose `K` as in (13), and set

```text
n_0(x,C) = max(n_*(x),3K,1).
```

For every integer `n>=n_0(x,C)`, choose `N=N_n`. It is a positive integer.
Equation (10), equation (13), and positivity of `N_n` yield

```text
C*n*E_x(n,N_n) = C*n*N_n < N_n*N_n = N_n^2.        (14)
```

Reading the choices in order:

```text
there exists G with P(G)=1 such that
  for every x in G,
    for every real C>0,
      there exists n_0(x,C)>=1 such that
        for every integer n>=n_0(x,C),
          there exists N>=1 (namely N_n) such that
            C*n*E_x(n,N) < N^2.
```

This is exactly T4's C1 quantifier pattern for almost every iid uniform
decimal stream.

It remains to justify that the set described by these real quantifiers is an
event. For every positive integer `q`, define

```text
H_q = union_(n_0>=1) intersection_(n>=n_0) union_(N>=1)
        {x : q*n*E_x(n,N) < N^2}.
```

For fixed `q,n,N`, the set in braces depends only on the finitely many
coordinates at starts `0,...,N-1` and their length-`n` look-ahead, hence is
measurable. Therefore `H_q` is measurable by countable closure, as is

```text
H = intersection_(integers q>=1) H_q.               (15)
```

The event `H` is exactly the event with `forall real C>0` in the theorem.
One direction is immediate by taking `C=q`. Conversely, if `x in H` and a
real `C>0` is given, choose a positive integer `q>C`. The eventual inequality
for `q` implies the same strict inequality for `C`, since `n>=1` and
`E_x(n,N)>=0`; hence `C*n*E_x(n,N)<=q*n*E_x(n,N)<N^2`. Thus integer
constants are cofinal for this monotone property.

The construction above proves `G subset H`. Since `G` and `H` are measurable,
`P(G)=1`, and `P(Omega)=1`, elementary measure fact 1 gives

```text
1 = P(G) <= P(H) <= P(Omega) = 1,
```

so `P(H)=1`. This verifies both the almost-sure quantifiers and the
measurability of the exact C1 event.

## Scope conclusion

The theorem proves that T5's generic disjunctive counterexample is exceptional
with respect to the iid uniform product measure: the exact C1 analogue holds
almost surely in this random model. It does not identify the decimal digits of
pi with a sample from that model and makes no pseudorandomness assumption about
pi. It therefore makes no claim about C1 for pi or canonical A1 for pi.
Nothing in the proof uses finite digit computation as evidence, let alone as
proof.
