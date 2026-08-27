# T39: exact four-row reduction to one orbit-shell inequality

Status: `proof sketch`.

The exact finite identities and inequalities below are derived from the
machine-checked T34 and T36 interfaces.  The terminal orbit-shell inequality
is an explicitly identified unproved premise.  Nothing in this note asserts
that `ARI_super`, `ARI_cancel`, C3, C2, or C1 holds.

## 1. Provenance and statement normalization

The canonical local problem has no external source URL.  A byte-exact copy is
delivered as `CANONICAL_STATEMENT.txt`.  Its verified SHA-256 is

```text
db1a5656ab93808f9729f08a2e0cae8c7612d5d3225b41ca791f5f381d90a0c3.
```

The canonical problem concerns the ordered long-lag collision count
`R_pi(m,N)`.  T39 does not estimate that count.  It concerns the residual
sparse-Fourier sibling A12 and, inside that sibling, only four rows of T36's
six-row `supercriticalIncidence`.

Fix natural numbers `Q0,Qstar`.  T36 defines

```text
ARI_superAt Q0 Qstar s C
```

to mean

```text
0 <= C and, for every natural m,N with 1 <= m and 1 <= N,

  supercriticalIncidence Q0 Qstar m N
    <= C [N + N^2 10^(-s m)].                              (1.1)
```

Its quantified predicate is

```text
for every real s, 0 < s < 1,
there exists C >= 0 satisfying (1.1) for every positive m,N. (1.2)
```

The four-row question in this note has exactly the quantifier order (1.2),
but with `supercriticalIncidence` replaced by its rows 2, 4, 5, and 6.  The
constant may depend on `Q0,Qstar,s`; it may not depend on `m,N`, a block, a
shell, or any row parameter.

Throughout Sections 3-8, `m,N` are natural numbers satisfying `1<=m` and
`1<=N`.  This positivity is essential when a weak inequality such as
`z+m<=v` is used to infer that the corresponding lag is strictly positive.

### Recorded ambiguities

1. This is a four-row assertion in sibling A12, not the canonical collision
   assertion.
2. `Q0,Qstar` are fixed before `s`; neither may vary with `m,N`.
3. The additive `N` and the term `N^2 10^(-s m)` are both literal.  Neither is
   discarded.
4. A fixed value of `m` cannot refute (1.2), because its second target term is
   still quadratic in `N`.
5. The T37 note is unverified motivation only and is not used as a premise.

## 2. Kernel-checked input

The accumulated machine-checked files used here are:

```text
T34CancellingRepunitIncidence.lean
SHA-256 720e5ee33f63226c560aee19751421fa383448e0aef45602c5eaf9a10f52778c

T36SubcriticalCancellationSaving.lean
SHA-256 3ba4c206ba517179b3561210acf37d704ec8d73a70155b23e55174c27ac0fc24
```

The relevant exported facts are as follows.

1. T34 defines the six row constructors, their filtered singleton domains,
   `repunitParameterDomain`, `cancellingValue`, the canonical shells, and the
   literal width-normalized incidence.
2. T32, imported by T34, states that a record belongs to a block exactly when
   it has positive lag, lag at least `m`, survives `ArithmeticExcluded`, and
   has its frequency endpoint in the block's half-open interval.
3. T24 and T29 define consecutive canonical blocks partitioning `[1,N)` and
   the width

   ```text
   w([a,b)) = sqrt(b^2-a^2).                               (2.1)
   ```

4. T36 defines the exact supercritical filter, the restricted shell sums, and
   the quantifiers in (1.1)-(1.2).

These inputs are kernel-checked.  The finite reductions made in this note are
new `proof sketch` arguments and are not presented as machine-checked.

## 3. Exact outer domain and coefficient

T34's outer parameter domain is

```text
D_N = {(v,rho): v<N, rho<N, 0<rho, v+rho<N}.               (3.1)
```

Put

```text
k = v+rho.
```

Then (3.1) is in bijection with

```text
0 <= v < k < N,                                            (3.2)
```

because `rho=k-v`; the separate condition `rho<N` follows from
`0<rho<=k<N`.  Under this change of variables the exact repunit coefficient is

```text
D(v,k) = cancellingValue(v,k-v)
       = 10^v(10^(k-v)-1)
       = 10^k-10^v.                                       (3.3)
```

T36's literal supercritical filter becomes

```text
P_(Qstar,m)(v,k):
  Qstar <= D(v,k) and 5m < 31k.                            (3.4)
```

No published irrationality estimate is assumed in (3.4).

## 4. Exact four rows

For an orientation `eps`, start `n`, and endpoint `E`, T34 uses

```text
record(eps,n,E) = (eps,(E-n,n)),                            (4.1)
```

where subtraction is natural-number subtraction.  Invalid endpoint order is
not silently interpreted: the resulting zero lag is rejected by the exact
block domain.

With `k=v+rho`, the four rows are exactly

```text
row 2, positiveSameStart:
  (record(true,z,v),  record(true,z,k));

row 4, negativeSameStart:
  (record(false,z,k), record(false,z,v));

row 5, mixedFirstEndpoint:
  (record(false,z,k), record(true,v,z));

row 6, mixedSecondEndpoint:
  (record(false,v,z), record(true,z,k)).                    (4.2)
```

Each row domain is a filtered singleton.  It has cardinality one precisely
when `rho>0` and both displayed records belong to T32's full block domain; it
has cardinality zero otherwise.  Thus all arithmetic-survival conditions and
both Bool orientations remain present.

For later use, define the survival indicator

```text
sigma_(Q0,m)(n,l) = 1 if not ArithmeticExcluded 8 1 Q0 m n l,
                    0 otherwise.                           (4.3)
```

The lag and block conditions are kept separate from (4.3).

## 5. Canonical block attached to an endpoint

The canonical block list is

```text
translatedCanonicalBlocks N
  = dyadicPartitionFrom 0 ((N-1).bitIndices.reverse).       (5.1)
```

The recursive definition places consecutive half-open blocks starting at
`1`; T24's sum-of-lengths identity says that their total length is `N-1`.
Consequently, for every integer `E` with `1<=E<N`, exactly one canonical block
contains `E`.  Existence follows by induction through the consecutive list,
and uniqueness is the machine-checked `canonicalBlock_interval_unique` lemma.

For `1<=k<N`, denote this block by

```text
B_N(k) = [a_N(k), b_N(k)),
W_N(k) = sqrt(b_N(k)^2-a_N(k)^2).                           (5.2)
```

Here `W_N(k)>0`, since `1<=a_N(k)<b_N(k)<=N`.

## 6. Exact shells and direct shell weight

For a real `x`, let

```text
delta(x) = |x-round(x)|,
K_m = clog_2(10^m)-1.                                      (6.1)
```

T34's endpoint conventions are

```text
S_0(m): 0 <= delta(x) <= 10^(-m),

S_j(m): 2^(j-1)/10^m < delta(x)
        <= min(2^j/10^m,1/2),  1<=j<=K_m.                 (6.2)
```

Thus shell zero is closed at `10^(-m)`, while every positive shell is open at
its lower endpoint and closed at its upper endpoint.  The final shell retains
the cap at `1/2`.

Every real lies in exactly one shell.  Define the literal shell coefficient

```text
theta_m(d) = 1       if d*pi lies in S_0(m),
             2^(-j) if d*pi lies in S_j(m), 1<=j<=K_m.     (6.3)
```

This is exactly T36's `shellWeight m ((d:real)*Real.pi)`, not an asymptotic
replacement.  Exchanging the finite block, parameter, and shell sums gives a
single factor `theta_m(D(v,k))` for each orbit coefficient.

## 7. Exact elimination of rows and blocks

Write `#X` for the cardinality of a finite set of integers.  For
`0<=v<k<N`, define

```text
H_ss(Q0,m;v,k)
  = #{z: 0<=z, z+m<=v,
         sigma_(Q0,m)(z,v-z)=1,
         sigma_(Q0,m)(z,k-z)=1},                           (7.1)
```

and, with `B_N(k)=[a,b)`,

```text
H_mix(Q0,m,N;v,k)
  = #{z: a<=z<b, v+m<=z, z+m<=k,
         sigma_(Q0,m)(v,z-v)=1,
         sigma_(Q0,m)(z,k-z)=1}.                           (7.2)
```

The ambient condition `z<N` from T34 is automatic in (7.1), since
`z<=v-m<v<N`, and in (7.2), since `z<b<=N`.

Rows 2 and 4 have the same two underlying long-pair cores.  T32's
orientation-invariance therefore makes their indicators equal.  Their two
frequency endpoints are `v,k`, so they occur in a canonical block precisely
when `v` also belongs to `B_N(k)`.  Hence their exact combined multiplicity is

```text
2 * 1_{a_N(k)<=v<b_N(k)} * H_ss(Q0,m;v,k).                 (7.3)
```

Rows 5 and 6 likewise have the same two underlying cores, with endpoints
`z,k`.  Their exact combined multiplicity is

```text
2 * H_mix(Q0,m,N;v,k).                                     (7.4)
```

The factor `2` in (7.3)-(7.4) counts the two named T34 row constructors.  It
is not T34's separate reversal factor from the complex cancelling-sector
identity; that reversal factor does not occur in `supercriticalIncidence`.

Let `A_4(Q0,Qstar;m,N)` be the literal contribution of rows 2, 4, 5, and 6 to
T36's `supercriticalIncidence`.  Equations (3.2)-(7.4) give the exact identity

```text
A_4(Q0,Qstar;m,N)
 = 2 * sum_{0<=v<k<N; P_(Qstar,m)(v,k)}
       theta_m(D(v,k)) / W_N(k)
       * [1_{a_N(k)<=v<b_N(k)} H_ss(Q0,m;v,k)
          + H_mix(Q0,m,N;v,k)].                            (7.5)
```

Identity (7.5) has eliminated the six-row finite-type sum, the canonical
block sum, and the positive-shell sum.  Its two cardinalities retain the
literal arithmetic-survival predicate, so (7.5) is exact rather than an
upper envelope.

Every summand is nonnegative.  Therefore `A_4` is a literal subincidence of
T36's full six-row `supercriticalIncidence`.

## 8. Elimination of hidden-exponent multiplicities

For an integer `t`, write

```text
[t]_+ = max(t,0).                                           (8.1)
```

The interval in (7.1), before arithmetic survival is imposed, contains
exactly

```text
L_ss(m;v) = [v-m+1]_+                                      (8.2)
```

integers.  The interval in (7.2), again before survival is imposed, is the
half-open integer interval

```text
[max(a_N(k),v+m), min(b_N(k),k-m+1)),
```

and therefore contains exactly

```text
L_mix(m,N;v,k)
 = [min(b_N(k),k-m+1)-max(a_N(k),v+m)]_+.                  (8.3)
```

Equations (8.2)-(8.3) remain valid when an interval is empty; using integers
in these formulas avoids any ambiguity from truncated natural subtraction.
Since each survival indicator is at most one,

```text
H_ss  <= L_ss,
H_mix <= L_mix.                                             (8.4)
```

Define the completely explicit geometric multiplicity

```text
Lambda_(m,N)(v,k)
 = 1_{a_N(k)<=v<b_N(k)} [v-m+1]_+
   + [min(b_N(k),k-m+1)-max(a_N(k),v+m)]_+.                (8.5)
```

Combining (7.5) and (8.4) gives, with the literal constant `2`,

```text
A_4(Q0,Qstar;m,N) <= E(Qstar;m,N),                         (8.6)

E(Qstar;m,N)
 = 2 * sum_{0<=v<k<N;
            Qstar<=10^k-10^v;
            5m<31k}
       Lambda_(m,N)(v,k) / W_N(k)
       * theta_m(10^k-10^v).                               (8.7)
```

There is no remaining sum over a block, hidden exponent `z`, row constructor,
or shell index in (8.7).  It is a double orbit sum with explicit geometric
multiplicity, exact canonical width, and exact endpoint-pinned shell weight.
It is independent of `Q0` because only the inequality
`sigma_(Q0,m)<=1` was used.

## 9. The one remaining orbit-shell inequality

The following is the strictly smaller quantified shell-clustering estimate
left by the reduction:

```text
(OSC_4)

For every fixed natural Qstar and every real s with 0<s<1,
there exists a real C_(s,Qstar)>=0 such that, for every natural m,N
with 1<=m and 1<=N,

  2 * sum_{0<=v<k<N;
          Qstar<=10^k-10^v;
          5m<31k}
        Lambda_(m,N)(v,k) / W_N(k)
        * theta_m(10^k-10^v)

  <= C_(s,Qstar) [N + N^2 10^(-s m)].                     (9.1)
```

All objects in (9.1) are explicit in (5.2), (6.1)-(6.3), and (8.5).  In
particular, (9.1) retains:

1. all positive `m,N`;
2. one constant before both scale variables;
3. the onset `Qstar<=10^k-10^v`;
4. the strict supercritical condition `5m<31k`;
5. the canonical block containing `k` and its literal square-root width;
6. the exact shell-zero and positive-shell endpoint conventions;
7. the two copies of each underlying row pattern; and
8. the complete target `N+N^2 10^(-s m)`.

By (8.6), `(OSC_4)` implies the required four-row bound for every `Q0`, with
the same constant.  It is a sufficient strengthening because arithmetic
survival was discarded in passing from (7.5) to (8.7).  No converse is
claimed.

This is now an orbit-shell clustering problem for the structured orbit

```text
{(10^k-10^v) pi : 0<=v<k<N},                              (9.2)
```

with deterministic weights `Lambda/W`.  Proving (9.1), or constructing a
fixed `s` and a growing-`m` family for which its exact four-row precursor
(7.5) has unbounded normalized ratio, is the unresolved arithmetic step.

## 10. Terminal conclusion and claim boundary

**Proof-sketch reduction.**  The exact four-row contribution is (7.5), and it
is bounded by the explicit orbit sum (8.7).  Thus the full four-row
forall-`s`/exists-`C_s`/forall-positive-`m,N` estimate follows from the single
displayed shell-clustering inequality `(OSC_4)` in (9.1), in which all block,
row, hidden-exponent, and shell-index sums have been eliminated.

The note does not prove `(OSC_4)` and does not provide a growing-`m`
refutation.  It therefore does not decide T36's full `ARI_super` predicate.
Rows 1 and 3 remain outside this analysis, and no conclusion about C3, C2, C1,
or the canonical collision count is inferred.

## 11. Verification map

1. Canonical statement and hash: delivered and byte-verified.
2. T34/T36 definitions and theorem interfaces: `machine-checked` input.
3. Equations (7.3)-(8.7): `proof sketch`, with every finite domain and constant
   displayed.
4. `(OSC_4)`: `conjecture`, isolated as the only terminal inequality.
5. Literature claim introduced: none.
6. Lean declarations introduced: none.
7. Independent statement and proof review: pending.
