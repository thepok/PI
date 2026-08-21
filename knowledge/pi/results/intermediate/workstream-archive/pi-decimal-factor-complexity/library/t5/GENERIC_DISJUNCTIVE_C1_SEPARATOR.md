# T5: A generic disjunctive decimal stream failing C1

Claim status: **proof sketch** (a complete elementary argument, awaiting
independent review).

This is a **generic sibling result**.  The stream constructed below is an
artificial decimal stream.  It is not the decimal expansion of pi.  Nothing
in this artifact asserts canonical A1, C1 for pi, disjunctivity of pi, or any
other property of pi.

## Source and scope

- Canonical statement: `knowledge/pi/statements/pi-decimal-factor-complexity.txt`
- SHA-256:
  `e2b6c9375936a97fe6cdd10c3f014613267f3c491935b536c6ec016c5f501e43`
- Original source URL: none is recorded; this is a local problem statement.
- Agenda item: T5, serving G5.

The accepted definitions reused here are those in:

- `knowledge_library/t1/DecimalFactorComplexity.lean`, especially
  `Stream`, `blockAt`, `Disjunctive`, `canonicalFactorComplexity`, and
  `decimal_disjunctive_iff_canonical_factorComplexity`;
- `knowledge_library/t4/FinitePrefixCollisionEnergy.lean`, especially
  `factorMultiplicity`, `collisionEnergy`, and `CollisionEnergyC1`.

No result from those files is re-proved except for the short counting facts
needed to make the present construction inspectable on paper.

## Normalized statement

Let `D = {0,1,...,9}`.  A decimal stream is a function
`s : N -> D`, indexed from zero.  For `n,N >= 0` and `v in D^n`, put

```text
m_s(n,N;v) = |{i : 0 <= i < N and (s(i),...,s(i+n-1)) = v}|,
E_s(n,N)   = sum_v m_s(n,N;v)^2.
```

The sum may be taken over all `v in D^n` or only over observed factors; the
unobserved terms are zero.  Thus this is exactly T4's collision energy among
the first `N` starting positions `0,...,N-1`.  Factors are allowed to extend
past position `N-1`.

T4's sibling condition is

```text
C1(s): for every real C > 0, there are n0 >= 1 such that
       for every n >= n0, there is N >= 1 with
       C n E_s(n,N) < N^2.
```

We prove the following.

**Theorem (generic separator).**  There is an explicitly defined decimal
stream `s` such that:

1. `s` is disjunctive.  Consequently its length-`n` factor complexity is
   `10^n` for every `n >= 1`.
2. There is a strictly increasing, hence unbounded, sequence
   `n_1,n_2,...` such that for every `j >= 1` and every `N >= 1`,

   ```text
   N^2 <= 4 n_j E_s(n_j,N).                         (1)
   ```

In particular, `C1(s)` is false: the fixed constant `C=4` has arbitrarily
large lengths at which no sample size `N` satisfies C1's strict inequality.

## Quantifier and convention checks

The following possible ambiguities are fixed throughout the proof.

- `N` counts starting positions, not a finite word containing the complete
  sampled factors.
- Collision energy includes diagonal ordered pairs; equivalently it is the
  sum of squared multiplicities.
- The witness `N` in C1 may depend on `n`.  Inequality (1) rules out every
  such `N`, not merely a selected subsequence of prefixes.
- To refute the eventual quantifier, the construction supplies unbounded bad
  lengths `n_j`, not merely one bad length.
- All coding intervals below are half-open integer intervals.
- The all-zero length-`n` word is denoted `0^n`.

## Explicit construction

For each integer `k >= 1`, list the `10^k` words in `D^k` in lexicographic
order:

```text
w_(k,0), w_(k,1), ..., w_(k,10^k-1).
```

Equivalently, `w_(k,q)` is the base-ten expansion of `q`, padded on the left
with zeros to exactly `k` digits.  Let

```text
U_k = w_(k,0) w_(k,1) ... w_(k,10^k-1),
ell_k = |U_k| = k * 10^k.
```

We now recursively define integers `e_k`, selected lengths `n_k`, and coding
coordinates `a_k`.  Start with `e_0=0`.  Once all data through stage `k-1`
are known, set

```text
n_k = e_(k-1) + 1.                                  (2)
```

For every `1 <= j <= k`, define the finite integer

```text
B_(j,k) = e_(j-1) + sum_(r=j)^k (ell_r + n_j).       (3)
```

Then set

```text
a_k = max_(1 <= j <= k) (4 B_(j,k) + n_j),          (4)
e_k = a_k + ell_k.                                  (5)
```

There is no circularity: in stage `k`, equation (2) uses only `e_(k-1)`;
all the `n_j` in (3) are then known; (3) uses the already explicit numbers
`ell_r`; and only after this are (4) and (5) evaluated.

Let the `k`th coding interval be

```text
I_k = [a_k,e_k).
```

The term with `j=k` in (4) gives

```text
a_k >= 4(e_(k-1) + ell_k + n_k) + n_k > e_(k-1).
                                                               (6)
```

Thus the intervals are disjoint and ordered:
`I_k` lies strictly after every earlier `I_r`.

Define `s : N -> D` by

```text
s(a_k+t) = U_k(t)  for 0 <= t < ell_k,
s(x)     = 0       when x belongs to no I_k.         (7)
```

The uniqueness needed in (7) follows from (6).  This also gives an effective
procedure for evaluating any requested digit `s(x)`: recursively compute the
stages until the first `k` with `a_k>x`; strict increase and unboundedness of
the natural numbers `a_k` guarantee termination.  Check the finitely many
earlier intervals for `x`; if one contains it, use the corresponding digit of
`U_r`, and otherwise return zero.  No later interval can contain `x`.
Equations (2)--(7) therefore define every digit explicitly, without an
infinite membership oracle.

## Disjunctivity

For `k=0`, the unique empty block occurs at position zero, so T1's
zero-length case is satisfied.  Now fix `k >= 1` and an arbitrary word
`w in D^k`.  It equals exactly one
`w_(k,q)` in the lexicographic list.  By the definition of `U_k`, its `k`
digits occur inside `U_k` beginning at offset `qk`.  By (7), they therefore
occur in `s` beginning at position `a_k+qk`.  Since this applies to every
natural `k` and every word in `D^k`, `s` is disjunctive in T1's exact sense.

There are exactly `10^k` possible length-`k` decimal words.  All of them
occur, so the factor set has exactly `10^k` elements.  This last conclusion
is also precisely the forward implication of the accepted machine-checked
theorem
`DecimalFactorComplexity.decimal_disjunctive_iff_canonical_factorComplexity`.

## Two elementary energy bounds

Fix any positive `n,N`.  The factor multiplicities partition the `N`
starting positions, so

```text
sum_v m_s(n,N;v) = N.                               (8)
```

Since `m^2 >= m` for every natural number `m`, (8) gives

```text
E_s(n,N) >= N.                                      (9)
```

Also, if `z` of the first `N` starts carry `0^n`, then the term belonging to
`0^n` alone gives

```text
E_s(n,N) >= z^2.                                    (10)
```

These statements agree with T4's multiplicity definition.  In particular,
(9) is the contribution of all diagonal collision pairs.

## The all-prefix counting invariant

Fix `j >= 1`, write `n=n_j`, and let `N>4n`.  Call a start `i<N` *bad* if
its length-`n` factor is not `0^n`; let `A` be the set of bad starts.

Outside the coding intervals the stream is zero.  Hence every bad factor
meets at least one coding interval.  This implication is intentionally only
one-way: a factor meeting a coding interval might still consist entirely of
zeros, which merely makes the following upper bound safer.

All intervals with index `r<j` are contained in `[0,e_(j-1))`.  A
nonnegative start whose factor meets one of them must itself be less than
`e_(j-1)`.  Therefore all earlier intervals together account for at most

```text
e_(j-1) = n_j-1 < n                                (11)
```

bad starts.

For one later interval `I_r=[a_r,e_r)`, the starts whose length-`n` factors
meet `I_r` lie in an integer interval of cardinality at most

```text
(e_r-a_r)+n = ell_r+n.                              (12)
```

Indeed, intersection requires both `i<e_r` and `a_r<i+n`; the possible
integer starts run from no earlier than `a_r-n+1` through `e_r-1`, a list of
at most `ell_r+n-1`, and (12) is a harmless weaker bound.

Only finitely many coding intervals meet factors beginning before `N`,
because (6) makes the `a_r` strictly increasing and unbounded.  There are two
cases.

### Case 1: no interval `I_r` with `r>=j` is met

By (11), `|A|<n`.  Since `N>4n`,

```text
4|A| < N.                                           (13)
```

### Case 2: at least one interval `I_r` with `r>=j` is met

Let `m` be the largest index of such an interval.  The union bound using
(11) and (12) gives

```text
|A| <= e_(j-1) + sum_(r=j)^m (ell_r+n_j)
     = B_(j,m).                                     (14)
```

Because `I_m` is met, some `i<N` and `t<n_j` satisfy `i+t in I_m`.  Hence

```text
a_m <= i+t < N+n_j.                                 (15)
```

The `j`th term is present in the maximum defining `a_m`, because `j<=m`.
Equations (4), (14), and (15) therefore imply

```text
4|A| <= 4B_(j,m) <= a_m-n_j < N.                   (16)
```

Combining the two cases proves the promised all-prefix invariant

```text
N>4n_j  implies  4|A|<N.                            (17)
```

No asymptotic density assertion was used: (17) applies to every individual
prefix length `N`, and its proof includes the look-ahead of length `n_j`
beyond the last sampled start.

## Collision-energy failure at every selected length

Fix `j>=1` and `N>=1`, and again write `n=n_j`.

If `N<=4n`, then (9) gives

```text
N^2 <= 4nN <= 4n E_s(n,N).                          (18)
```

Suppose instead that `N>4n`.  Let `z=N-|A|`, the number of starts carrying
`0^n`.  From (17), in particular `2|A|<=N`, so

```text
N <= 2(N-|A|) = 2z.
```

Using (10) and `n>=1`, we obtain

```text
N^2 <= 4z^2 <= 4E_s(n,N) <= 4nE_s(n,N).             (19)
```

Equations (18) and (19) prove (1) for every `N>=1`.

## Exact failure of C1

The selected lengths are unbounded.  Indeed, (6) gives
`e_k>e_(k-1)`, so by (2)

```text
n_(k+1)=e_k+1 > e_(k-1)+1=n_k.
```

Now fix the positive real constant `C=4`.  Given any proposed threshold
`n0>=1`, choose `j` with `n_j>=n0`.  At this particular `n=n_j`, (1) says
for every `N>=1`, after coercion to the reals,

```text
N^2 <= 4 n E_s(n,N).
```

Thus there is no `N>=1` satisfying C1's required strict inequality
`4 n E_s(n,N)<N^2`.  Since this happens beyond every proposed `n0`, the
quantified statement `CollisionEnergyC1 s` is false.

## Conclusion

The explicitly defined artificial stream (7) is disjunctive and has maximal
factor complexity `10^n` at every positive length, yet it fails the exact C1
analogue.  Therefore disjunctivity, and even maximal factor complexity, does
not imply C1 for a generic decimal stream.  This separates the sibling
condition C1 from factor-language richness alone.  It makes no claim about
pi or canonical A1.
