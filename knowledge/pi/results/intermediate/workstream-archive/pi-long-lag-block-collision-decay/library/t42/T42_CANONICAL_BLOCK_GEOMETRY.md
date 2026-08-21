# T42: sharp canonical-block geometry for the four-row incidence

Status: `proof sketch`.  The T24, T29, T31, T32, T34, and T36 interfaces cited
below are machine-checked.  The finite regrouping and elementary geometry
proof in this note are fully displayed, but have not been formalized in Lean.

## 1. Scope, provenance, and claim boundary

The canonical local problem has no external source URL.  A byte-exact copy is
delivered as `CANONICAL_STATEMENT.txt`; its verified SHA-256 is

```text
db1a5656ab93808f9729f08a2e0cae8c7612d5d3225b41ca791f5f381d90a0c3.
```

That statement asks for a bound on the ordered long-lag collision count
`R_pi(m,N)`.  This note does not estimate that count.  It treats only the
four same-start and mixed rows inside T36's residual sparse-Fourier sibling
A12.  In particular, this note proves neither `OSC_4` nor `ARI_super`,
`ARI_cancel`, C3, C2, C1, or the canonical collision estimate.

The T39 note is unverified motivation only.  No assertion from T39 is used as
a premise: the row domains, finite regrouping, multiplicity envelope, and
geometry estimate are reconstructed below from the kernel-checked files.

The phrase "uniform fixed-`k` bound" has two possible meanings.  This note
resolves both:

1. no absolute constant, independent of `k`, bounds the normalized geometry;
2. for each fixed `k`, the strict bound `G_(m,N)(k) < k` is uniform over every
   positive `m` and every `N>k`, and its leading constant `1` is optimal.

Thus the sharp worst-case replacement scaling is `Theta(k)`, not `Theta(1)`.

## 2. Kernel-checked input

The exact accumulated files used here, with SHA-256 values verified in this
session, are

```text
T24MaximalToLocalReduction.lean
2795d228eab081360e236be14ae99c0dd8267153d39e680710732330ea586924

T29WidthWeightedSquareFunction.lean
2f18966e04e00eb657d4a517d31281f9e8eafae4a6365bcf0985b94711e1e358

T31CrossBlockAlmostEverywhere.lean
535a43fc06ac84d9b61760300c642fc05dbd797dc7cedb25f0ed30156bf10380

T32AllBlockFixedPiRange.lean
3bb7e8a1fc13a87dd6decba4edd7dd1aa4daef51233b585e2e48e81bb2e78fdc

T34CancellingRepunitIncidence.lean
720e5ee33f63226c560aee19751421fa383448e0aef45602c5eaf9a10f52778c

T36SubcriticalCancellationSaving.lean
3ba4c206ba517179b3561210acf37d704ec8d73a70155b23e55174c27ac0fc24
```

The relevant public interfaces are:

1. T24: `canonicalDyadicPartition`, its exact block lengths, and its
   endpoint telescope over `[1,N)`.
2. T29: `translatedCanonicalBlocks`, `widthWeight`,
   `translatedCanonicalBlock_spec`, `canonical_widthWeight_pos`, and
   `canonical_finish_le`.
3. T31: `canonicalBlock_interval_unique`.
4. T32: `mem_blockRecordDomain_iff` and
   `blockRecordDomain_both_orientations`.
5. T34: the six `CancellingRow` constructors, the six row membership
   theorems, `mem_repunitParameterDomain_iff`, the shell definitions, and
   `shellIndex_mem`.
6. T36: `Supercritical`, `restrictedWeightedShellIncidence_eq_direct`,
   `inDyadicShell_unique`, and `ARI_super_iff_quantifiers`.

No irrationality-measure estimate is used in the geometry argument.

## 3. Quantifiers and exact T36 data

Fix arbitrary natural numbers `Q0,Qstar`.  Unless explicitly stated
otherwise, let `m,N` be natural numbers satisfying

```text
1 <= m,  1 <= N.                                           (3.1)
```

The fixed-constant predicate in T36 places one real constant before all such
`m,N`.  The onset parameters `Q0,Qstar` are fixed before `s`, and neither may
vary with `m,N`.

### 3.1 Outer parameters and supercritical filter

T34's exact outer domain is

```text
D_N = {(v,rho): v<N, rho<N, 0<rho, v+rho<N}.               (3.2)
```

Set

```text
k = v+rho,  d(v,k) = 10^v(10^(k-v)-1) = 10^k-10^v.        (3.3)
```

The change `(v,rho) -> (v,k)` is a bijection from (3.2) to

```text
0 <= v < k < N,                                            (3.4)
```

with inverse `rho=k-v`.  Indeed, `0<rho` is exactly `v<k`, and the separate
condition `rho<N` follows from `rho<=k<N`.

T36's literal supercritical condition is

```text
P_(Qstar,m)(v,k):
  Qstar <= 10^k-10^v  and  5m < 31k.                      (3.5)
```

The second inequality is strict.

### 3.2 Record domain and arithmetic survival

For orientation `eps`, start `n`, and endpoint `E`, T34 defines

```text
record(eps,n,E) = (eps,(E-n,n)),                            (3.6)
```

where subtraction is natural subtraction.  T32's exact membership theorem
says that `(eps,(r,n))` lies in the block record domain for a half-open block
`B=[a,b)` exactly when

```text
0 < r,
m <= r,
not ArithmeticExcluded(8,1,Q0,m,n,r),
a <= n+r < b.                                              (3.7)
```

An invalid endpoint order in (3.6) gives lag zero and is rejected by (3.7).
Define the literal survival indicator

```text
sigma_(Q0,m)(n,r)
  = 1 if not ArithmeticExcluded(8,1,Q0,m,n,r),
    0 otherwise.                                           (3.8)
```

T32's `blockRecordDomain_both_orientations` shows that (3.7), hence (3.8),
is independent of the Bool orientation.

### 3.3 Canonical blocks and widths

T24 and T29 define

```text
B_N = translatedCanonicalBlocks N
    = dyadicPartitionFrom 0 ((N-1).bitIndices.reverse).     (3.9)
```

For a block `B=(a,j)`,

```text
B.start = a,  B.finish = a+2^j,
w(B) = sqrt(B.finish^2-B.start^2).                         (3.10)
```

The recursive definition makes the blocks consecutive, beginning at `1`.
Their lengths sum to `N-1`.  Therefore every integer `E` with `1<=E<N`
belongs to some block.  A direct induction on the list in (3.9) proves
existence: the first block covers the first `2^j` integers and the recursive
tail starts at its excluded endpoint.  Uniqueness is the kernel-checked T31
theorem `canonicalBlock_interval_unique`.  Consequently, for `1<=k<N` there
is a unique block

```text
B_N(k) = [a_N(k),b_N(k)),
W_N(k) = sqrt(b_N(k)^2-a_N(k)^2) > 0.                      (3.11)
```

The endpoints satisfy

```text
1 <= a_N(k) <= k < b_N(k) <= N.                           (3.12)
```

### 3.4 Exact shell weights

Put

```text
delta(x) = |x-round(x)|,
K_m = clog_2(10^m)-1.                                     (3.13)
```

For positive `m`, T34 proves `1<=K_m`,
`10^m<=2^(K_m+1)`, and `2^K_m<10^m`.  Its exact shells are

```text
S_0(m,x): 0 <= delta(x) <= 10^(-m),

S_j(m,x): 2^(j-1)/10^m < delta(x)
            <= min(2^j/10^m,1/2),  1<=j<=K_m.             (3.14)
```

Thus shell zero is closed at `10^(-m)`, every positive shell is open below
and closed above, and the terminal shell retains the cap at `1/2`.  The
literal weight is

```text
theta_m(d)
  = 1_(S_0(m,d*pi))
      + sum_(j=1)^K_m 2^(-j) 1_(S_j(m,d*pi)).              (3.15)
```

This is exactly T34/T36's
`shellWeight m ((d:real)*Real.pi)`.  T34's `shellIndex_mem` and shell
disjointness from T36's `inDyadicShell_unique` show that exactly one summand
in (3.15) is active.

## 4. The literal four rows

Let `k=v+rho`.  Rows 2, 4, 5, and 6 of T34 are exactly

```text
row 2, positiveSameStart:
  (record(true,z,v),  record(true,z,k));

row 4, negativeSameStart:
  (record(false,z,k), record(false,z,v));

row 5, mixedFirstEndpoint:
  (record(false,z,k), record(true,v,z));

row 6, mixedSecondEndpoint:
  (record(false,v,z), record(true,z,k)).                    (4.1)
```

For each displayed row, T34's domain is the singleton containing that record
pair, filtered by `0<rho` and membership of both records in (3.7).  Its
cardinality is therefore exactly zero or one.  The hidden exponent has the
literal range

```text
z in Finset.range N, equivalently 0<=z<N.                  (4.2)
```

There is no extra orientation factor in these row cardinalities.  The factor
two below counts the two explicitly named rows in each pair.  It is not
T34's separate reversal factor in `cancellingSectorContribution`; that
reversal factor is absent from T36's `supercriticalIncidence`.

## 5. Exact finite regrouping

Define `A_4(Q0,Qstar;m,N)` directly from T36 by replacing the six-row sum in
`blockRepunitMultiplicity` with the four-element set of rows in (4.1), while
leaving unchanged:

1. every block in `B_N`;
2. every `(v,rho)` in `D_N` satisfying (3.5);
3. every `z` in `range N`;
4. every row-domain cardinality;
5. division by the literal `w(B)`; and
6. multiplication by the literal shell weight (3.15).

Equivalently, before regrouping,

```text
A_4
 = sum_(B in B_N)
     sum_((v,rho) in D_N; Supercritical(Qstar,m)(v,rho))
       theta_m(cancellingValue(v,rho)) / w(B)
       * sum_(0<=z<N) sum_(r in {2,4,5,6})
           card(cancellingRowDomain(8,1,Q0,m,B,r,v,rho,z)). (5.1)
```

All sums in (5.1) are finite.  T36's
`restrictedWeightedShellIncidence_eq_direct` justifies replacing the original
shell-zero plus positive-shell sum by (3.15).  Finite distributivity then
permits the block, parameter, hidden-exponent, and row sums to be reordered
without convergence assumptions.

For `B_N(k)=[a,b)`, define

```text
H_ss(Q0,m;v,k)
 = #{z: 0<=z, z+m<=v,
        sigma_(Q0,m)(z,v-z)=1,
        sigma_(Q0,m)(z,k-z)=1},                            (5.2)

H_mix(Q0,m,N;v,k)
 = #{z: a<=z<b, v+m<=z, z+m<=k,
        sigma_(Q0,m)(v,z-v)=1,
        sigma_(Q0,m)(z,k-z)=1}.                            (5.3)
```

The upper condition `z<N` in (5.2) is automatic because
`z<=v-m<v<N`.  It is automatic in (5.3) because `z<b<=N`.

For rows 2 and 4, (3.7) gives `z+m<=v`; this also implies `z+m<=k`.
Their endpoints are `v,k`.  Both records can lie in one canonical block
exactly when `v` lies in `B_N(k)`.  Orientation invariance makes the two row
indicators equal.  Their combined multiplicity, after summing over `z`, is

```text
2 * 1_{a<=v<b} * H_ss(Q0,m;v,k).                           (5.4)
```

For rows 5 and 6, the two lag conditions are `v+m<=z` and `z+m<=k`;
their endpoints are `z,k`.  Both endpoints lie in one block exactly when
`z` lies in `B_N(k)`.  Again the two row indicators agree, and their combined
multiplicity is

```text
2 * H_mix(Q0,m,N;v,k).                                    (5.5)
```

Using the bijection (3.4), uniqueness of `B_N(k)`, (5.4), and (5.5) in
(5.1) gives the exact identity

```text
A_4(Q0,Qstar;m,N)
 = 2 * sum_(0<=v<k<N; P_(Qstar,m)(v,k))
       theta_m(10^k-10^v) / W_N(k)
       * [1_{a_N(k)<=v<b_N(k)} H_ss(Q0,m;v,k)
          + H_mix(Q0,m,N;v,k)].                            (5.6)
```

This derivation retains the exact arithmetic-survival predicates.  In
particular, (5.6) is an identity, not an asymptotic estimate.

## 6. The full geometric multiplicity envelope

For an integer `x`, write `[x]_+=max(x,0)`.  Before arithmetic survival is
imposed, the `z` interval in (5.2) has exactly

```text
L_ss(m;v) = [v-m+1]_+                                     (6.1)
```

members.  The interval in (5.3) is

```text
[max(a_N(k),v+m), min(b_N(k),k-m+1)),                     (6.2)
```

so it has exactly

```text
L_mix(m,N;v,k)
 = [min(b_N(k),k-m+1)-max(a_N(k),v+m)]_+.                 (6.3)
```

These integer formulas include empty intervals without truncated-natural
subtraction.  Since each survival indicator is at most one,

```text
H_ss <= L_ss,  H_mix <= L_mix.                             (6.4)
```

Define the complete geometric envelope

```text
Lambda_(m,N)(v,k)
 = 1_{a_N(k)<=v<b_N(k)} [v-m+1]_+
   + [min(b_N(k),k-m+1)-max(a_N(k),v+m)]_+.               (6.5)
```

Equations (5.6) and (6.4) prove, with the literal row factor `2`,

```text
A_4(Q0,Qstar;m,N) <= E_4(Qstar;m,N),                      (6.6)

E_4(Qstar;m,N)
 = 2 * sum_(0<=v<k<N;
            Qstar<=10^k-10^v;
            5m<31k)
       [Lambda_(m,N)(v,k)/W_N(k)]
       * theta_m(10^k-10^v).                              (6.7)
```

The parameter `Q0` disappears only in the inequality (6.6), because (6.4)
discards arithmetic survival.  The onset `Qstar`, strict supercritical
filter, exact orbit value, and exact shell weight remain.

## 7. Sharp fixed-`k` geometry theorem

For positive `m`, `1<=k<N`, define the full normalized geometric sum

```text
G_(m,N)(k)
 = sum_(v=0)^(k-1) Lambda_(m,N)(v,k)/W_N(k).               (7.1)
```

Let `B_N(k)=[a,b)`, and put

```text
L=b-a,  d=k-a.                                             (7.2)
```

By (3.12), `L>0` and `0<=d<L`.  Since `v<k<b` and `m>=1`, (6.5) simplifies
exactly to

```text
Lambda_(m,N)(v,k)
 = 1_{a<=v}[v-m+1]_+
   + [k-m+1-max(a,v+m)]_+.                                 (7.3)
```

### 7.1 Exact sum formula

For an integer `x`, define

```text
T(x) = q(q+1)/2, where q=[x]_+.                            (7.4)
```

Summing the first term in (7.3) over `a<=v<k` gives

```text
T(k-m)-T(a-m).                                             (7.5)
```

The second term counts pairs `(v,z)` satisfying

```text
a<=z<=k-m,  0<=v<=z-m.                                    (7.6)
```

Indeed, fixing `v` in (7.6) gives exactly the integer interval counted by
the second term of (7.3).  Reversing these two finite sums gives

```text
sum_(z=a)^(k-m) [z-m+1]_+
 = 0,                                      if d<m,
   T(k-2m+1)-T(a-m),                       if d>=m.         (7.7)
```

Therefore the exact numerator in (7.1) is

```text
sum_(v=0)^(k-1) Lambda_(m,N)(v,k)
 = T(k-m)-T(a-m)
   + if d<m then 0 else T(k-2m+1)-T(a-m).                 (7.8)
```

This is the full multiplicity sum, including both same-start and mixed
pieces, not a bound on only one row type.

### 7.2 Uniform linear upper bound

Increasing `m` can only shorten both intervals in (7.3).  Hence, pointwise,

```text
Lambda_(m,N)(v,k) <= Lambda_(1,N)(v,k).                    (7.9)
```

At `m=1`, the sum is particularly simple.  For `0<=v<a`, the mixed term is
`k-a=d` and the same-start term is zero.  For `a<=v<k`, the two terms sum to

```text
v + (k-v-1) = k-1.
```

There are `a` values in the first range and `d` in the second, so

```text
sum_(v=0)^(k-1) Lambda_(1,N)(v,k)
 = ad+d(k-1)
 = d(a+k-1)
 = k(k-1)-a(a-1).                                         (7.10)
```

It remains to compare (7.10) with the literal width.  As

```text
W_N(k)^2 = b^2-a^2 = L(2a+L),                             (7.11)
```

consider, for real `x>=0`,

```text
f(x) = x(2a+x)/(a+x) = a+x-a^2/(a+x).                     (7.12)
```

The last expression shows directly that `f` is increasing.  Since `d<L`,

```text
d(2a+d)/(a+d)
 <= L(2a+L)/(a+L)
  = W_N(k)^2/b
 <= W_N(k).                                                (7.13)
```

The final inequality follows from `0<W_N(k)<=b`, which in turn follows from
`W_N(k)^2=b^2-a^2<=b^2`.  Since `a+d=k`, (7.13) gives

```text
d(2a+d) <= k W_N(k).                                      (7.14)
```

If `d=0`, (7.10) is zero.  If `d>0`, then
`d(2a+d-1)<d(2a+d)`.  Combining (7.9)-(7.14) and dividing by the positive
width proves the explicit uniform bound

```text
0 <= G_(m,N)(k) < k                                       (GB_k)
```

for every positive `m` and every `N>k`.  The coefficient `1` in `(GB_k)` is
independent of `m,N`, the block endpoints, `Q0`, and `Qstar`.

### 7.3 Infinite counterfamily to an absolute bound and sharpness

Let `r>=2` and set

```text
L=2^r,  N=L+1,  m=1,  k=L.                                (7.15)
```

Here `N-1=2^r` has one nonzero binary digit, so (3.9) consists of the single
canonical block

```text
B_N(k)=[1,L+1),  W_N(k)=sqrt(L^2+2L).                     (7.16)
```

Putting `a=1`, `d=L-1`, and `k=L` into (7.10) gives the exact value

```text
G_(1,L+1)(L) = L(L-1)/sqrt(L^2+2L),                       (7.17)

G_(1,L+1)(L)/L = (L-1)/sqrt(L^2+2L).                      (7.18)
```

For `L>=4`,

```text
L^2+2L <= 4(L-1)^2
```

because the difference is `3L^2-10L+4>=0`.  Thus (7.17) gives

```text
G_(1,L+1)(L) >= L/2 = k/2.                                (7.19)
```

As `r` tends to infinity, the ratio in (7.18) tends to `1`.  Consequently:

1. no absolute constant uniformly bounds all `G_(m,N)(k)`;
2. the worst-case scaling is exactly `Theta(k)`;
3. the leading coefficient `1` in `(GB_k)` is optimal, although the strict
   upper bound is not attained by this family.

This counterfamily is a purely geometric statement about `Lambda/W`.  It is
not a counterfamily to T36's full incidence or to `ARI_super`, because it
does not impose the orbit shell weight or arithmetic survival.

## 8. Substitution: a lower-dimensional orbit-only inequality

The shell weight in (6.7) still depends on `v`, so `(GB_k)` cannot replace the
inner sum by a single shell weight without an additional operation.  Define
the finite onset-filtered orbit set

```text
V_Qstar(k) = {v: 0<=v<k, Qstar<=10^k-10^v},               (8.1)
```

and define the maximum, with value zero on an empty set,

```text
M_(m,Qstar)(k)
 = max_{v in V_Qstar(k)} theta_m(10^k-10^v).               (8.2)
```

Every term in (6.7) is nonnegative.  For a fixed `k`, restricting the
`v`-sum to (8.1), bounding its shell weights by (8.2), and then enlarging the
geometric sum to every `0<=v<k` gives

```text
sum_(v in V_Qstar(k))
  [Lambda_(m,N)(v,k)/W_N(k)] theta_m(10^k-10^v)
 <= M_(m,Qstar)(k) G_(m,N)(k)
 <= k M_(m,Qstar)(k).                                     (8.3)
```

Substitution into (6.7) yields the explicit orbit-only domination

```text
A_4(Q0,Qstar;m,N)
 <= E_4(Qstar;m,N)
 <= 2 * sum_(1<=k<N; 5m<31k) k M_(m,Qstar)(k).            (8.4)
```

The factor `2` is still exactly the two copies in (5.4)-(5.5).  Formula
(8.4) has no canonical block, width, row, hidden-exponent, or `v`-sum.  Its
only arithmetic object is the finite maximum over the orbit shell values
`(10^k-10^v)pi`.

The resulting lower-dimensional sufficient orbit-shell predicate is:

```text
(OMSC_4)

For every fixed natural Qstar and every real s with 0<s<1, there exists
a real C_(s,Qstar)>=0 such that, for all positive natural m,N,

  2 * sum_(1<=k<N; 5m<31k) k M_(m,Qstar)(k)
    <= C_(s,Qstar) [N + N^2 10^(-s m)].                   (8.5)
```

By (8.4), `(OMSC_4)` would imply the required bound for the literal four-row
contribution for every `Q0`, with the same constant.  It is smaller in the
precise structural sense requested here: the block, width, row,
hidden-exponent, and `v`-sum have disappeared.  It is not asserted to have a
smaller numerical left side.  Logically it is a sufficient strengthening,
not an equivalence, because taking a maximum discards correlation between
`Lambda` and the shell values.  No proof of (8.5) is claimed here.

Replacing `M_(m,Qstar)(k)` merely by `1` would give a quadratic sum and would
discard the orbit-shell saving.  Therefore (8.5), rather than an unweighted
sum over `k`, is the honest remaining orbit-only frontier produced by the
geometry theorem.

## 9. What is and is not resolved

The following statements are established by the displayed finite arguments:

1. the exact four-row identity (5.6), reconstructed from T34/T36;
2. the explicit geometric envelope (6.5)-(6.7), with constant `2`;
3. the exact full fixed-`k` sum (7.8);
4. the uniform bound `(GB_k)`;
5. the infinite family (7.15)-(7.19), proving sharp `Theta(k)` scaling and
   refuting every absolute geometry bound; and
6. the orbit-only domination (8.4).

The unresolved input is (8.5), an orbit-shell clustering estimate at the
fixed phase `pi`.  Rows 1 and 3 are also outside this four-row analysis.
Accordingly, this note does not assert `OSC_4`, `ARI_super`, `ARI_cancel`, C3,
C2, C1, or the canonical collision bound.

## 10. Verification checklist

1. Canonical source and hash: Section 1 and `CANONICAL_STATEMENT.txt`.
2. Positive `m,N` and constant dependence: Section 3.
3. Outer domain and fixed-`k` range: (3.2)-(3.5).
4. Literal record domain and survival: (3.6)-(3.8).
5. Canonical blocks and exact width: (3.9)-(3.12).
6. Every shell endpoint and weight: (3.13)-(3.15).
7. Four exact row records and hidden range: (4.1)-(4.2).
8. Finite regrouping and factor `2`: (5.1)-(5.6).
9. Full normalized multiplicity: (6.1)-(7.8).
10. Uniform bound and sharp counterfamily: `(GB_k)` and (7.15)-(7.19).
11. Smaller orbit-only inequality and constants: (8.1)-(8.5).
12. Literature claims introduced: none.
13. Lean declarations introduced: none.
14. Independent statement and proof review: pending.
