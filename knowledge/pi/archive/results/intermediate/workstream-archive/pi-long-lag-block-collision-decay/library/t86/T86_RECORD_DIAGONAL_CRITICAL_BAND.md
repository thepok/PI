# T86: record diagonal in the exact critical band

Classification: `proof sketch`.

The imported T22, T24, T29, and T32 interfaces cited below are
`machine-checked`. The new all-`m` deductions in this note are rigorous finite
algebra, but they have not been formalized in Lean and therefore remain a
`proof sketch` under the program vocabulary.

## 1. Provenance, scope, and normalized statement

The canonical local statement is vendored as `CANONICAL_STATEMENT.txt`; it has
no external source URL. Its SHA-256 is

```text
db1a5656ab93808f9729f08a2e0cae8c7612d5d3225b41ca791f5f381d90a0c3
```

The canonical question concerns ordered nonoverlapping decimal-block
collisions. This note instead analyzes T29's residual sparse-Fourier sibling
A12. It neither weakens nor answers the canonical question.

Fix arbitrary `Q0 : Nat`, put `(mu,c)=(8,1)`, and let `m,N` be positive
integers satisfying the exact critical-band inequalities

```text
H = 10^m,                 H <= N^2 <= 2H.                 (1.1)
```

The phase is `alpha=pi`, as in C2, although the record diagonal isolated here
is phase-independent. The exponent is fixed at `s=1/2`. T29's literal target,
including its outer inclusive-frequency factor, is

```text
Q(m,N) = H * scaleMatchedTarget(1/2,m,N)
       = H * (N + N^2/sqrt(H)).                           (1.2)
```

The quantifiers are simultaneous over every positive `m,N` satisfying (1.1),
not only over T85's tested cases. The constant `Q0` is arbitrary and the final
formula is independent of it.

Recorded interpretation choices:

1. "Record diagonal" means the `q=r` part of T32's ordered record-pair
   expansion, before adding the centered off-diagonal Dirichlet terms.
2. "Endpoint depth" of a canonical block `[a,b)` means `d=N-b`, its distance
   from the strict cutoff endpoint.
3. "Short-terminal tail" means all canonical blocks after the unique largest
   first block. A level-`q` terminal suffix means those tail blocks of length at
   most `2^q`.
4. Every arithmetic exclusion is retained until Section 3 proves, uniformly
   in all variables, that none occurs for `(mu,c)=(8,1)`.

## 2. Imported checked interfaces

No prior note is used as a discharged premise. The following declarations are
from kernel-checked modules in the accumulated library.

| Item | Imported declaration | Literal information used |
|---|---|---|
| T22 | `mem_orderedLongPairDomain_iff_admissible_endpoint` | Positive lag, `m <= r`, strict endpoint cutoff, and the arithmetic exclusion |
| T22 | `both_orientations_exact` | Both Boolean orientations and their opposite signed frequencies |
| T24 | `canonicalDyadicPartition_levels` | Canonical block levels are the decreasing nonzero binary digits of `N-1` |
| T24 | `canonicalDyadicPartition_endpoint_telescope` | The blocks exactly partition `[1,N)` |
| T29 | `mem_inclusiveFrequencies_iff` | The literal frequency domain is `1 <= h <= 10^m` |
| T29 | `translatedCanonicalBlock_spec` | Every block is `[a,a+2^j)` with the translated alignment |
| T29 | `widthWeight_eq_endpoints` | The literal divisor is `sqrt(b^2-a^2)` |
| T29 | `canonical_widthWeight_sum_le_sharp` | The checked bound `sum_B w_B <= (3/2+sqrt(2))N` |
| T32 | `mem_blockRecordDomain_iff` | Block records have `a <= n+r < b`, with all admissibility clauses |
| T32 | `blockRecordDomain_both_orientations` | Both ordered orientations survive together |
| T32 | `blockSquaredEnergy_eq_diagonal_add_offDiagonal` | Every record-diagonal pair contributes exactly `10^m` |
| T32 | `widthWeightedSquareFunction_eq_diagonal_add_offDiagonal` | The diagonal and centered off-diagonal terms retain the literal block widths |

T79's kernel-checked `arithmeticExcluded_iff_explicit` expands the exclusion
predicate as follows. For

```text
q = 10^n * (10^r-1),
```

`ArithmeticExcluded mu c Q0 m n r` is exactly

```text
Q0 <= q  and  10^(-m) <= q * (c/q^mu).                  (2.1)
```

This is an expansion of the inherited T25 definition, not a new assumption.

## 3. All-scale arithmetic-exclusion audit

We prove that (2.1) is false for every record in the present parameters. Let
`m>=1`, `r>=m`, `n>=0`, and `H=10^m`. Then `H>=10` and

```text
q = 10^n(10^r-1) >= 10^m-1 = H-1 > 0.                 (3.1)
```

At `(mu,c)=(8,1)`, the second conjunct of (2.1) is

```text
1/H <= q/q^8 = 1/q^7,
```

which, because `H,q>0`, would imply `q^7<=H`. On the other hand,

```text
(H-1)^2-H = H^2-3H+1 >= 10^2-3*10+1 = 71 > 0.
```

Since `H-1>=1`, (3.1) gives

```text
q^7 >= (H-1)^7 >= (H-1)^2 > H.                         (3.2)
```

This contradicts the exclusion inequality. Thus, independently of `Q0`,

```text
not ArithmeticExcluded 8 1 Q0 m n r                    (3.3)
```

for every `m>=1`, `r>=m`, and `n>=0`. This is a new all-`m` proof; T12's
machine-checked `not_arithmeticExcluded_eight_one_at_one` covers only `m=1`,
and T85 checked only its finite tested scales.

## 4. Exact records at one endpoint

For an integer `K>=0`, define

```text
L_m(K)   = max(K-m,0),
Phi_m(K) = L_m(K) * (L_m(K)+1).                         (4.1)
```

Fix an endpoint `E=n+r`. T22 admissibility, T32 block membership, and (3.3)
leave exactly

```text
m <= r <= E,       n=E-r,
```

when `E>=m`, and no records when `E<m`. Hence there are exactly
`(E-m+1)` cores at endpoint `E>=m`. T22 retains both Boolean orientations, so
the literal ordered-record multiplicity at `E` is

```text
2 * max(E-m+1,0).                                       (4.2)
```

The number of records with strict endpoint below `K` is therefore

```text
2 * sum_{E=0}^{K-1} max(E-m+1,0)
  = 2 * sum_{t=1}^{L_m(K)} t
  = Phi_m(K).                                           (4.3)
```

Consequently, for every T29 canonical block `B=[a,b)`, T32's literal block
domain has the exact cardinality

```text
M_B := card(blockRecordDomain 8 1 Q0 m B)
     = Phi_m(b)-Phi_m(a)
     = 2 * sum_{E=a}^{b-1} max(E-m+1,0).                (4.4)
```

This derives every summand directly from the imported domains. In the useful
case `a>=m`, (4.4) simplifies to

```text
M_B = (b-a)(a+b-2m+1).                                  (4.5)
```

No orientation, endpoint, exclusion, or strict-cutoff convention has been
dropped.

## 5. Exact diagonal formula

T29 sums over exactly `H` inclusive positive frequencies. T32's diagonal has
one pair `(q,q)` per ordered record and its Dirichlet kernel is exactly `H`.
The width is literally `w_B=sqrt(b^2-a^2)`. Thus the record diagonal in T29's
width-weighted square function is

```text
D(m,N) = H * sum_{B=[a,b) in translatedCanonicalBlocks(N)}
                 (Phi_m(b)-Phi_m(a)) / sqrt(b^2-a^2).   (5.1)
```

Formula (5.1) is finite, exact, independent of `alpha` and `Q0`, and valid for
all positive `m,N`; the critical band is needed only for the bounds below.

As a direct check of all conventions, at the smallest critical pair
`(m,N)=(1,4)`, the binary blocks are `[1,3)` and `[3,4)`. Both contain six
ordered records, so

```text
D(1,4) = 10 * (6/sqrt(8) + 6/sqrt(7)).                  (5.2)
```

In particular, the inclusive endpoint contributes `10`, not `11`.

## 6. Canonical-block endpoint-depth decomposition

Write the unique binary expansion in decreasing levels as

```text
N-1 = sum_{i=0}^r ell_i,       ell_i=2^(j_i),
j_0 > j_1 > ... > j_r >= 0.                              (6.1)
```

Set `S_{-1}=0`, `S_i=sum_{u=0}^i ell_u`. T24's canonical blocks are exactly

```text
B_i=[a_i,b_i)=[1+S_{i-1},1+S_i).                        (6.2)
```

Define their endpoint depths

```text
d_i=N-b_i=sum_{u=i+1}^r ell_u.                          (6.3)
```

All lower binary levels are smaller than `j_i`, hence

```text
0 <= d_i <= sum_{k=0}^{j_i-1}2^k = ell_i-1.             (6.4)
```

Equations (6.2)-(6.3) give

```text
a_i=N-d_i-ell_i,    b_i=N-d_i,
b_i^2-a_i^2=ell_i(2N-2d_i-ell_i).                       (6.5)
```

Substitution in (5.1) is the requested exact depth decomposition:

```text
D(m,N)/H = sum_{i=0}^r
  [Phi_m(N-d_i)-Phi_m(N-d_i-ell_i)]
  / sqrt(ell_i(2N-2d_i-ell_i)).                         (6.6)
```

The literal rightmost block has `d_r=0`. Formula (6.6) exposes every block,
including every short terminal block, without replacing its width by an
asymptotic surrogate.

## 7. Two-sided normalized critical-band bounds

First, for every block `[a,b)`, (4.4) and `m>=1` give

```text
Phi_m(b)-Phi_m(a)
 <= 2 * sum_{E=a}^{b-1} E
  = (b-a)(a+b-1)
 <= b^2-a^2.                                            (7.1)
```

Therefore its summand in (5.1) is at most `sqrt(b^2-a^2)`. Applying T29's
machine-checked sharp width-sum bound gives

```text
D(m,N)/H <= (3/2+sqrt(2))N.                             (7.2)
```

For the lower bound, every canonical endpoint satisfies `b<=N`, so each
literal width is at most `N`. All numerators are nonnegative, and the blocks
partition `[1,N)`. Hence they telescope without changing any denominator:

```text
D(m,N)/H
 >= (1/N) * sum_B (Phi_m(b)-Phi_m(a))
  = Phi_m(N)/N.                                         (7.3)
```

The critical band implies

```text
N >= 4m.                                                (7.4)
```

For `m=1`, this follows from `N^2>=10`, so `N>=4`. For `m>=2`, prove
`10^m>=16m^2` by induction: the base is `100>=64`; multiplying by ten
dominates the replacement of `m^2` by `(m+1)^2` because
`10m^2>=(m+1)^2` for `m>=1`. Then `N^2>=10^m>=16m^2` gives (7.4).

It follows that `N-m>=3N/4`, and (7.3) yields

```text
D(m,N)/H >= (N-m)(N-m+1)/N >= 9N/16.                   (7.5)
```

Finally, (1.1) gives

```text
1 <= N/sqrt(H) <= sqrt(2),
2HN <= Q(m,N) <= (1+sqrt(2))HN.                         (7.6)
```

Combining (7.2), (7.5), and (7.6) proves the explicit all-scale bounds

```text
9/[16(1+sqrt(2))]
 <= D(m,N)/Q(m,N)
 <= 3/4 + sqrt(2)/2.                                    (7.7)
```

Equivalently, rationally weakened but convenient constants are

```text
1/5 < D(m,N)/Q(m,N) < 3/2.                              (7.8)
```

Indeed, `9/[16(1+sqrt(2))]=9(sqrt(2)-1)/16>1/5`, while
`3/4+sqrt(2)/2<3/2`. The weak inequalities in (7.7) include either
critical-band endpoint whenever it is attained. In fact the lower endpoint is
attained for even `m`, while `2*10^m` is never an integer square.

## 8. Short terminal blocks are bounded, not growing

Let `P=ell_0`, the unique largest binary length. Since
`P<=N-1<2P`, integrality gives

```text
N <= 2P.                                                (8.1)
```

The leading block is `B_0=[1,P+1)`. For `m>=2`, one has `m<=P/4`.
For `m=2`, (1.1) gives `10<=N<=14`, hence `P=8`. For `m>=3`, induction gives
`10^m>64m^2`, so `N>8m`; combine this with (8.1).

The leading contribution is exactly

```text
D_0/H = (P+1-m)(P+2-m) / sqrt(P(P+2)).                  (8.2)
```

Using `m<=P/4` and `sqrt(P(P+2))<P+1`, the numerator in (8.2) is at least
`(3P/4+1)(3P/4+2)`, which is greater than `9P(P+1)/16`. Therefore

```text
D_0/H > 9P/16.                                         (8.3)
```

Let `T` be the sum of all blocks after `B_0`; this is the short-terminal tail.
Every such block starts at least at `P+1>m`, so (4.5) applies. If its length is
`ell`, its exact contribution obeys

```text
D_B/H
 = sqrt(ell(a+b)) * (1-(2m-1)/(a+b))
 <= sqrt(ell(a+b))
 <= sqrt(2N ell)
 <= 2sqrt(P ell).                                       (8.4)
```

The terminal lengths are distinct powers among `1,2,...,P/2`. Thus

```text
sum_{B in T} sqrt(ell_B)
 <= sum_{j=0}^{j_0-1} 2^(j/2)
  = (sqrt(P)-1)/(sqrt(2)-1)
  < (1+sqrt(2))sqrt(P).                                 (8.5)
```

Equations (8.3)-(8.5) give

```text
T/D_0 < 32(1+sqrt(2))/9,
T/D(m,N) < 32(1+sqrt(2)) / [9+32(1+sqrt(2))] < 9/10.    (8.6)
```

For the only `m=1` critical pair, `N=4`. From (5.2), the terminal fraction is

```text
(6/sqrt(7)) / (6/sqrt(8)+6/sqrt(7))
 = 2sqrt(2)/(sqrt(7)+2sqrt(2)) < 2/3.                  (8.7)
```

Hence (8.6) is valid for every positive critical pair: the complete
short-terminal tail is uniformly bounded away from total concentration. It
does not consume a growing fraction of the diagonal mass.

There is a sharper depth statement. For `q<j_0`, let `T_q` be the sum over
terminal blocks with `j_i<=q`, equivalently length at most `2^q`. The finite
geometric sum gives

```text
sum_{j=0}^q 2^(j/2) < (2+sqrt(2))sqrt(2^q).
```

For `m>=2`, define

```text
A_q = [32(2+sqrt(2))/9] * sqrt(2^q/P).                  (8.8)
```

Repeating (8.4)-(8.5) only over these levels proves

```text
T_q/D_0 < A_q,       T_q/D(m,N) < A_q/(1+A_q).          (8.9)
```

Thus genuinely short terminal blocks, with `2^q/P -> 0`, carry an explicitly
vanishing `O(sqrt(2^q/P))` fraction. The classification required by T86 is
therefore **bounded**, with constants (8.6) and (8.9), rather than growing.
No asymptotic oscillation claim is needed or made.

## 9. What the diagonal does not decide

T32's exact identity is

```text
full block energy = record diagonal + centered off-diagonal Dirichlet sum.
```

The full T29 square function is nonnegative, but the centered off-diagonal
piece is signed block by block. It may cancel part of the positive diagonal or
add to it. Moreover, C2 allows a constant `A_(1/2)` rather than requiring the
constant one. Therefore diagonal excess alone does not refute C2. The bounded
terminal fraction identifies the centered fixed-`pi` off-diagonal remainder,
not endpoint geometry, as the next cancellation frontier.

This note makes no C1 claim and no C3 claim.

## 10. T85 is heuristic motivation only

T85 is classified `experiment`, with replay verification recorded in
`REPLAY_RECEIPT.txt`. Its finite transition cases motivated examining the
record diagonal and canonical endpoint geometry. No T85 numerical observation
is used in Sections 3-8. In particular:

1. T85's finite ratios neither prove nor refute C2.
2. T85 does not prove the all-`m` exclusion statement (3.3).
3. T85 does not prove the universal bounds (7.7), (8.6), or (8.9).
4. T85 concerns T29's A12 sibling, not the canonical collision count.
5. T85's own documentation states that it makes no C1 or C3 claim.

Relevant replay-certified T85 pins are:

```text
REPLAY.md          421d1d304c7ed7da61e9a7fa34eb4d80c29e76c2affa2cbd2a46cf12d11447ff
REPLAY_RECEIPT.txt bd7097ca5f6998dfaaa2ccf0c699ff0a61fa12a860cc9f94ccf622bce9417fa8
results.json       2f7baabf87783601a8361f9041c214cb30e5d31a8c1cf1cd9780a3966791f2cf
```

## 11. Search and claim audit

Search date: 2026-08-06.

The accumulated kernel-checked T22, T24, T29, T32, and T79 modules were
searched before deriving new notation. Their existing domain, partition,
width, and diagonal interfaces are imported above rather than duplicated.
The T85 replay package was inspected only for finite motivation and claim
limits. No external theorem or literature claim is needed for the finite
algebra in this note, and no novelty claim is made.

Claim status: `proof sketch`. The exact formula and constants await either Lean
formalization or independent expert checking before any stronger label.
