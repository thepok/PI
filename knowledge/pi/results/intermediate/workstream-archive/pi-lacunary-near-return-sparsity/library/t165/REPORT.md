# T165: explicit collision bound for finite Champernowne prefixes

Audit date: 2026-08-12 UTC.

The universal argument in Sections 2--7 is a `proof sketch`: it is written out
with explicit constants but is not Lean-formalized. Section 8 is a finite
`experiment`, not evidence for the universal claim. Section 9 records prior
fingerprints at their supplied verification levels. Section 10 is a separate
`conjecture` and unproved pi transfer. The result is only a `related-model`
statement about a finite Champernowne word.

```text
EXTERNAL_LITERATURE_USED: none
T160_USED_AS_PREMISE: no
FINITE_VALIDATION_IS_PROOF: no
FIXED_PI_CLAIM: none
A1_CLAIM: none
C1_CLAIM: none
C2_CLAIM: none
SCOPED_VERDICT_COUNT: 1
AUTOMATIC_SUCCESSOR_COUNT: 0
```

## 1. Immutable question, scope, and ambiguities

The canonical question was formulated locally on 2026-07-22 and has no
external source URL. The byte-exact `canonical_statement.txt` has SHA-256

```text
cbf56699b651aeb69301265763e38da44feb59c6fd955d2280887e8c06c6a2f8.
```

It fixes the decimal orbit of pi, strict circle distance, ordered pairs with
the diagonal included, and quantifiers
`forall A exists n0 forall n>=n0 exists N`. This note does not alter or answer
that question. Exact equality of finite decimal blocks in an artificial word
is the weaker A10/A14 sibling.

The agenda's ambiguous terms are fixed as follows.

1. `W_K` ends after the decimal representation of `10^K-1`; there is no
   decimal point, separator, padding, or cyclic wrap.
2. Starts and digit offsets are zero-based. Endpoints are inclusive.
3. Every legal overlapping start is retained, including starts crossing one
   or more integer boundaries.
4. Energy counts ordered pairs and includes every diagonal pair.
5. A start's stratum and alignment are determined by the integer containing
   its first digit, not its last digit.
6. A power-of-ten rollover is separated from ordinary carries. Ordinary carry
   length is the number of trailing nines in the left integer.
7. The growing-depth range is `1<=m<=floor(K/4)`. For arbitrary `A`, the
   useful uniform tail is `2A<=m<=floor(K/4)`.
8. T160 is motivation and comparison memory only. No definition, lemma,
   source statement, or deduction from T160 is a premise below.

## 2. Prefix, starts, endpoints, multiplicities, and energy

Write `dec(n)` for the usual base-ten representation of positive `n`, with no
leading zero. For `K>=1`, define

```text
W_K = dec(1) dec(2) ... dec(10^K-1),
L_K = |W_K| = sum_(d=1)^K 9*d*10^(d-1)
    = [1+(9K-1)10^K]/9.                                  (2.1)
```

Also set `L_0=0`. Fix `1<=m<=L_K`. The legal starts, inclusive endpoint, and
number of starts are

```text
I_(K,m)={0,1,...,L_K-m},
e(i,m)=i+m-1,
M_(K,m)=|I_(K,m)|=L_K-m+1.                                (2.2)
```

The block at `i` is the literal substring

```text
B_(K,m)(i)=W_K[i] W_K[i+1] ... W_K[e(i,m)].                (2.3)
```

For `w in {0,...,9}^m`, define

```text
c_(K,m)(w)=#{i in I_(K,m):B_(K,m)(i)=w},
E_(K,m)=sum_w c_(K,m)(w)^2.                               (2.4)
```

Expanding each square gives the exact ordered-pair identity

```text
E_(K,m)=#{(i,j) in I_(K,m)^2:B_(K,m)(i)=B_(K,m)(j)}.       (2.5)
```

Thus all `M_(K,m)` diagonal pairs occur. Overlap between the two blocks is
unrestricted; if `|i-j|<m`, exactly `m-|i-j|` digit coordinates overlap.

## 3. Exhaustive start and pair taxonomy

Every digit position belongs to a unique `dec(n)`. For a legal start `i`, let

```text
n(i) = the integer whose representation contains W_K[i],
d(i) = |dec(n(i))|,
a(i) = offset of W_K[i] in dec(n(i)),  0<=a(i)<d(i).        (3.1)
```

The **integer-length stratum** is `d(i)` and the **within-integer alignment**
is `a(i)`. Let `b(i)=d(i)-a(i)` be the number of digits of `n(i)` beginning at
the start. There are two main classes.

1. `LOW`: `d(i)<m`. The block can cross several integer boundaries.
2. `HIGH`: `d(i)>=m`. If `b(i)>=m`, the block is `INTERNAL`; if `b(i)<m`, it
   is `CROSSING` and crosses exactly the boundary `n(i)|n(i)+1`.

For every crossed boundary `n|n+1`, define

```text
lambda(n)=max{t>=0:n == 10^t-1 (mod 10^t)},                (3.2)
```

the number of trailing nines. An ordinary boundary has `n<10^d-1` and carry
type `tau=min(lambda(n),b)`, where `b` is the number of inspected suffix
digits. The values `tau=0,...,b` are exhaustive; `tau=b` means that the carry
leaves the inspected suffix. The exceptional boundary `n=10^d-1` has type
`ROLLOVER(d)` because the successor has `d+1` digits. A `LOW` start is refined
by the ordered list of all crossed boundary records
`(digit length, ordinary tau or rollover)`. This list is finite and uniquely
determined by the start and endpoint.

An ordered equal-block pair `(i,j)` is classified by the ordered pair of these
complete start records. This gives strata `(d(i),d(j))`, alignments
`(a(i),a(j))`, both boundary signatures, and every carry type. Reversing a
pair generally changes its class, as required by ordered energy. The diagonal
lies in the equal-record classes. Since every legal start has exactly one
record, these class products are disjoint and exhaustive, and summing their
equal-word products is exactly (2.5).

## 4. One-class multiplicity bound

Fix `K>=1`, `m>=1`, a word `w`, a high stratum `m<=d<=K`, and alignment
`0<=a<d`. Put `b=d-a`.

### 4.1 Internal alignment

If `b>=m`, the block fixes `m` specified decimal positions of the `d`-digit
integer `n`. The remaining `d-m` positions have at most ten choices each.
The no-leading-zero restriction can only reduce the count, so

```text
#{starts of type (d,a,INTERNAL) carrying w} <= 10^(d-m).   (4.1)
```

### 4.2 Ordinary boundary and all carry lengths

Suppose `b<m` and put `r=m-b`. Because `d>=m`, one has `1<=r<=d` and the
block reaches only `n+1`. Let `s` be the integer represented by the first `b`
digits of `w`, allowing leading zeros, and let `p` be the integer represented
by its final `r` digits. An ordinary crossing occurrence must satisfy

```text
n == s (mod 10^b),
p*10^(d-r) <= n+1 <= (p+1)10^(d-r)-1.                    (4.2)
```

After subtracting one, the second line is an interval of exactly
`10^(d-r)` consecutive integers. Moreover

```text
d-r-b=d-m>=0,                                              (4.3)
```

so its length is divisible by `10^b`. Every complete interval of that length
contains exactly

```text
10^(d-r)/10^b=10^(d-m)                                    (4.4)
```

members of each residue class modulo `10^b`. Intersecting with the ordinary
`d`-digit range can only remove members. Equations (4.2)--(4.4) use the actual
successor `n+1`; therefore they include, without an independence assumption,
every ordinary carry length `tau=0,...,b`. Refining by any fixed `tau` only
decreases the count.

### 4.3 Power-of-ten boundary

For fixed `d,a`, at most one start has `n=10^d-1`. It exists only when `d<K`
and its endpoint is legal. It is the sole `ROLLOVER(d)` contribution. Thus,
combining ordinary and rollover crossings,

```text
#{starts of high type (d,a) carrying w} <= 10^(d-m)+1.     (4.5)
```

The `+1` is deliberately retained even for internal alignments and for `d=K`,
where it is unnecessary. This makes the later sum uniform.

## 5. Uniform word multiplicity

All starts anchored in strata `d<m` begin before the end of `dec(10^(m-1)-1)`.
There are exactly `L_(m-1)` digit positions there, so, regardless of their
multi-boundary and carry signatures, at most `L_(m-1)` such starts carry a
fixed `w`. Summing (4.5) over every high stratum and alignment gives the
constant-explicit bound

```text
c_(K,m)(w) <= B_(K,m),
B_(K,m)=L_(m-1)+sum_(d=m)^K d*(10^(d-m)+1).                (5.1)
```

This is already a closed finite formula. For the advertised growing range,
assume

```text
K>=4,             1<=m<=floor(K/4).                       (5.2)
```

Then

```text
sum_(d=m)^K d*10^(d-m)
 <= K*10^(K-m)*sum_(t=0)^infinity 10^(-t)
 = (10/9)K*10^(K-m),                                      (5.3)

sum_(d=m)^K d <= K^2,                                     (5.4)

L_(m-1) <= m*10^(m-1).                                    (5.5)
```

From `4m<=K`, `2m<=K`, hence `10^(m-1)<=10^(K-m)`, and
`m<=K/4`. Also `K<=10^(K-m)` for `K>=4` and `4m<=K`
(for example, group the exponent into at least `floor(K/2)` decimal factors;
the elementary inequality `K<=10^floor(K/2)` starts at `K=4` and is preserved
when `K` increases). Therefore (5.4)--(5.5) give

```text
K^2+L_(m-1)
 <= K*10^(K-m)+(K/4)*10^(K-m)
 = (5/4)K*10^(K-m).                                      (5.6)
```

Since `10/9+5/4=85/36<3`, equations (5.1)--(5.6) yield

```text
max_w c_(K,m)(w) <= 3K*10^(K-m).                           (5.7)
```

No assertion from T160 occurs in this derivation.

## 6. Ordered collision theorem with constants

For nonnegative integer multiplicities summing to `M`,

```text
sum_w c_w^2 <= (max_w c_w)*sum_w c_w=M*max_w c_w.          (6.1)
```

The last digit-length stratum alone contributes `9K*10^(K-1)` digits. Under
(5.2),

```text
M_(K,m)=L_K-m+1
 >=9K*10^(K-1)-m+1
 >=8K*10^(K-1).                                           (6.2)
```

Combining (5.7), (6.1), and (6.2) proves the related-model proposition

```text
E_(K,m)/M_(K,m)^2 <= 15/(4*10^m)                           (6.3)
```

for every `K>=4` and `1<=m<=floor(K/4)`.

Consequently, for every integer `A>=1`, throughout the same range and whenever

```text
15*A*m <= 4*10^m,                                         (6.4)
```

one has the requested ordered, diagonal-inclusive bound

```text
E_(K,m) <= M_(K,m)^2/(A*m).                               (6.5)
```

This division denotes a rational inequality; equivalently
`A*m*E_(K,m)<=M_(K,m)^2`, with no rounding ambiguity.

## 7. Explicit growing-depth corollaries

For `A=1`, (6.4) holds for every `m>=1`: it starts with `15<=40`, and
`10^m/m` strictly increases. Thus (6.5) holds uniformly over the full declared
range

```text
K>=4,                 1<=m<=floor(K/4).                    (7.1)
```

For arbitrary integer `A>=1`, condition (6.4) holds whenever `m>=2A`.
Indeed it is enough to check `m=2A`; the elementary bounds
`A^2<=10^A` and `30<=4*10^A` give

```text
15*A*(2A)=30A^2 <=30*10^A <=4*10^(2A),                    (7.2)
```

and again `10^m/m` increases. Therefore, for every `A>=1` and `K>=8A`,

```text
2A<=m<=floor(K/4)  implies
A*m*E_(K,m)<=M_(K,m)^2.                                   (7.3)
```

This is a pair-sensitive growing-depth theorem for the named finite prefixes
`W_K`, with constants `3`, `8`, `15/4`, `2`, and `8` exposed. It is not a
normality argument and does not select unrelated prefixes after seeing `m`:
the same explicit family `W_K` works throughout each displayed row.

## 8. Finite validation (`experiment`)

From a directory containing only the delivered files, run

```text
python3 verify_t165.py > replay.txt
diff -u raw_output.txt replay.txt
sha256sum -c SHA256SUMS
```

The verifier constructs `W_K` directly for `1<=K<=4` and bounded `m`. For
every legal start it independently records the anchor integer, stratum,
alignment, endpoint, all crossed boundaries, every ordinary carry length, and
every rollover. It checks:

1. the exact length and start formulas (2.1)--(2.2);
2. the multiplicity histogram and ordered diagonal-inclusive identity (2.5),
   with literal `M^2` pair enumeration on every tested case having `M<=600`;
3. the exhaustive product-of-start-classes reconstruction of energy on every
   tested case, including the larger prefixes where literal `M^2` enumeration
   would be wasteful;
4. the internal and boundary per-`(d,a,w)` bounds (4.1), (4.5);
5. the low-stratum budget and exact bound (5.1);
6. the simplified constants (5.7), (6.2)--(6.4) on a bounded arithmetic grid;
7. the canonical statement hash and required report markers.

These computations can catch indexing, endpoint, carry, classification, and
constant errors. They do not prove Sections 4--7.

## 9. Prior and active fingerprint comparison

Verification levels are load-bearing. Unverified notes are comparison memory,
not discharged premises.

| Item | Supplied level and fingerprint | T165 boundary |
|---|---|---|
| T2 | `machine-checked`; normal decimal streams, including the artificial Champernowne stream, satisfy a sibling near-return quantifier pattern via eventual block-frequency bounds | T165 imports no T2 theorem. It treats the specific cutoffs `W_K`, exact equal blocks rather than metric neighbors, and proves an explicit uniform `K,m` pair bound. T2 prevents this from being advertised as the first Champernowne sibling result. |
| T94/T97 | accepted notes at `sketch`; their reports argue, unverified, for exact finite-state paperfolding collision recurrences and a dyadic diagonal formula | T165 uses decimal integer strata and successor arithmetic, not paperfolding decimation or a finite profile recurrence. No T94/T97 claim is a premise. |
| T121 | source claims `literature-checked`, deductions `proof sketch`, replay `experiment`; aggregate Walsh/Parseval collision mechanisms and exact necklace blocks | T165 has no Fourier transform or necklace. It first proves a pointwise multiplicity bound from decimal substrings and then applies the elementary `E<=M*cmax` inequality. |
| T158 | source claims `literature-checked`, deductions `proof sketch`, replay `experiment`; the note argues that an expanding empirical transition kernel loses deterministic Euler ordering | T165 retains the actual increasing-integer order and counts successor intervals directly. It uses no empirical kernel, gap, conductance, or T158 deduction. |
| T160 | source claims `literature-checked`, deductions `proof sketch`, replay `experiment`; motivation includes a base-2 Champernowne lower-bound card at one sparse depth and a pair-multiplicity diagnostic | T160 is not a premise. T165 independently starts from (2.1)--(2.5), works in base ten at all depths in (7.1)/(7.3), and obtains an upper bound. This is the nearest disclosed motivational overlap. |
| T162 | source claims `literature-checked`, deductions `proof sketch`, replay `experiment`; minimum return separation is proposed as a sufficient order-aware certificate | T165 does not require equal blocks to be separated: adjacent or overlapping equal starts are included in the same multiplicity fibers. The mechanism is arithmetic fiber counting, not a return-gap premise. |
| active T163 | active lease recorded in the supplied snapshot; no artifact or agenda content was readable | Identifier reserved. No fingerprint, availability inference, premise, or nonduplication claim is made beyond the observed active status. |
| active T164 | active lease recorded in the supplied snapshot; no artifact or agenda content was readable | Identifier reserved under the same firewall. If its later artifact overlaps decimal successor counting, novelty and duplication must be reassessed; T165 does not infer its content. |

The exact duplication boundary is therefore: T2 already supplies a
machine-checked normality-based Champernowne sibling with existential cutoffs;
T160 already identifies direct pair multiplicity as a useful diagnostic. The
new related-model proof sketch here is only the elementary, constant-explicit
all-`W_K` bound (5.1)--(7.3). No novelty claim is made.

## 10. Separate unproved pi-specific premise

**PI-ARITHMETIC-FIBER-T165 (`conjecture`; UNPROVED PI TRANSFER; NOT
ASSERTED).** A transfer toward the machine-checked T7 symbolic interface would
need, for every `A>=1` and all sufficiently large decimal depths `m`, an actual
pi prefix with `N` starts and a pi-specific arithmetic classification of every
ordered equal length-`m` block pair into explicit witness fibers such that

```text
sum_(witness fibers F) |F| <= N^2/(A*m),                   (10.1)
```

where the fibers are disjoint, retain both pair orientations and all diagonal
pairs, and their capacity bounds follow from an identity special to pi rather
than from an assumed occupancy, collision, discrepancy, or Fourier bound.
Equivalently, a one-coordinate classification may prove
`max_w c_m^pi(w)<=N/(A*m)` and then use (6.1), but that maximum-multiplicity
estimate is itself the unproved pi-specific premise.

For transfer toward T107, (10.1) is not enough: one must additionally prove
T107's common-prefix triangular synchronization, active boundary budgets, and
collected Fourier remainder budgets at their stated constants. For the
canonical metric count, exact block equality is weaker than strict circle near
return, so the separately machine-checked symbolic-to-metric comparisons and
their constants must be applied in the correct direction; T165 supplies no
such pi input.

The decimal successor relation used in (4.2) belongs to the artificial word
`W_K`. Decimal digits of pi are not consecutive integer representations, so
copying (4.2) to pi would be invalid. There is no fixed-pi, A1, C1, or C2
claim.

## 11. Endpoint

`SCOPED VERDICT (1/1): HOLD AS MODEL.`

Hold the finite base-ten Champernowne prefixes as a constant-explicit
pair-sensitive calibration model: (7.3) gives the requested growing-depth
energy bound, while the proof exposes exactly how ordinary carries and the
single power-of-ten rollover are paid. The scope is only this related model;
it supplies no evidence for the unproved pi premise in Section 10. There is no
automatic successor.
