# T169: sharp collision asymptotic for finite Champernowne prefixes

Audit date: 2026-08-13 UTC. Sections 2--8 are a `proof sketch`, not
machine-checked. Section 9 is an `experiment` used only to falsify identities
and endpoint conventions. This is an A10/A14 `related-model` result. It is not
a result about the fixed decimal orbit of pi.

```text
CANONICAL_SHA256: cbf56699b651aeb69301265763e38da44feb59c6fd955d2280887e8c06c6a2f8
FINITE_CHECKS_ARE_PROOF: no
T160_USED_AS_PREMISE: no
T165_USED_AS_PREMISE: no
FIXED_PI_CLAIM: none
A1_CLAIM: none
C1_CLAIM: none
C2_CLAIM: none
```

## 1. Scope, normalized statement, and ambiguities

The byte-exact local source is `canonical_statement.txt`; the source URL is
local (`knowledge/pi/statements/pi-lacunary-near-return-sparsity.txt`), because the
canonical question was formulated by this program rather than copied from an
external source. It asks whether

```text
forall A>=1, exists n0, forall n>=n0, exists N>=1:
    A*n*Q_pi(n,N) <= N^2,
```

where `Q_pi` counts ordered, diagonal-inclusive strict circle near returns.
T169 answers none of that. It studies exact equality of blocks in an artificial
finite word, hence the A10/A14 sibling.

The agenda's quantifiers and conventions are normalized as follows.

1. `K>=4` and `1<=m<=floor(K/4)` unless explicitly stated otherwise.
2. `W_K` stops at the final digit of `10^K-1`; there is no separator, padding,
   decimal point, or cyclic wrap.
3. Starts are zero-based and endpoints inclusive. Every overlapping legal
   start is counted, including starts crossing integer boundaries.
4. Pairs are ordered and include the diagonal.
5. A start's stratum and alignment come from the integer containing its first
   digit. Carry length is the number of trailing nines in the left integer;
   `10^d-1 | 10^d` is separately a rollover.
6. The assertion is uniform over all displayed `m`, not merely fixed `m` as
   `K` grows.

## 2. Exact word, starts, multiplicities, and energy

Let `dec(n)` be the usual decimal representation of positive `n`, without
leading zeros. Put

```text
W_K = dec(1) dec(2) ... dec(10^K-1),
L_d = |W_d| = sum_(q=1)^d 9*q*10^(q-1)
    = [1+(9d-1)10^d]/9,             L_0=0.                 (2.1)
```

For `1<=m<=L_K`, define

```text
I_(K,m)={0,...,L_K-m},
e(i,m)=i+m-1,
M_(K,m)=L_K-m+1,
B_(K,m)(i)=W_K[i]...W_K[e(i,m)],                           (2.2)
c_(K,m)(w)=#{i in I_(K,m):B_(K,m)(i)=w},
E_(K,m)=sum_(w in {0,...,9}^m) c_(K,m)(w)^2.               (2.3)
```

Expanding the squares gives the exact ordered, diagonal-inclusive identity

```text
E_(K,m)=#{(i,j) in I_(K,m)^2:B_(K,m)(i)=B_(K,m)(j)}.       (2.4)
```

Thus all `M_(K,m)` diagonal pairs occur. Blocks may overlap: when
`|i-j|<m`, they share exactly `m-|i-j|` digit coordinates.

## 3. Exhaustive start and pair classes

Every digit position lies in a unique `dec(n)`. For a legal start `i`, let
`n(i)` be that integer, let `d(i)=|dec(n(i))|`, and let `a(i)` be the offset of
the start in `dec(n(i))`, so `0<=a(i)<d(i)`. The complete start record is

```text
C(i)=(d(i),a(i),S(i)),                                    (3.1)
```

where `S(i)` is the ordered list of all boundaries crossed before `e(i,m)`.
Each entry is one of

```text
ORDINARY(q,t): the boundary n|n+1 has q-digit left member and
               t=the exact number of trailing nines of n,
ROLLOVER(q):   n=10^q-1 and n+1=10^q.                     (3.2)
```

For `d(i)>=m`, the block crosses at most one boundary. It is `INTERNAL` when
`d(i)-a(i)>=m`; otherwise its singleton signature is `ORDINARY(d,t)` or
`ROLLOVER(d)`. For `d(i)<m`, the finite ordered list records every crossing.
For an ordinary `q`-digit boundary, `0<=t<=q-1`; thus carries extending beyond
the inspected suffix remain distinct exact classes. This covers every exact
carry length, multiple low-stratum crossings, and every power-of-ten rollover.

For each record `alpha`, set

```text
c_alpha(w)=#{i in I_(K,m):C(i)=alpha and B_(K,m)(i)=w}.    (3.3)
```

Every start has exactly one record, so the exact pair decomposition is

```text
E_(K,m)=sum_(ordered alpha,beta) sum_w c_alpha(w)c_beta(w).(3.4)
```

The classes are disjoint and exhaustive. The order of `(alpha,beta)` retains
both pair orientations; diagonal pairs occur in `alpha=beta` summands. This is
the requested decomposition by integer-length stratum, alignment, boundary
crossing, every carry type, and rollover. The following argument first sums
the carry-refined classes exactly, then centers their total multiplicities.

## 4. Exact high-stratum count

Fix `m<=d<=K`, alignment `0<=a<d`, and word
`w=w_0...w_(m-1)`. If the block is internal (`a+m<=d`), fixing its `m`
digits in a `d`-digit integer gives exactly

```text
1[w_0!=0]*10^(d-m)          if a=0,
9*10^(d-m-1)                if 1<=a<=d-m.                  (4.1)
```

The second line includes the nine choices for the unfixed leading digit; it is
used only when `d-m>=1`.

Now suppose `a+m>d`, put `b=d-a` and `r=m-b`. The block specifies the last
`b` digits `s` of `n` and first `r` digits `p` of `n+1`. Ordinary occurrences
satisfy

```text
n == s (mod 10^b),
p*10^(d-r) <= n+1 <= (p+1)10^(d-r)-1.                    (4.2)
```

The interval after subtracting one has length `10^(d-r)`, divisible by
`10^b` because `d-r-b=d-m`. Hence it has exactly `10^(d-m)` members of the
required residue class. It lies in the `d`-digit range exactly when the first
digit of `p`, namely `w_b`, is nonzero. In that case its only possible
out-of-range member is the lower endpoint `n=10^(d-1)-1`, and it occurs exactly
when

```text
w = rho_(d,a):=9^b 1 0^(r-1).                             (4.3)
```

For that same word, the rollover start anchored at `n=10^d-1` has alignment
`a`, suffix `9^b`, and successor prefix `10^(r-1)`. If `d<K`, it is legal and
restores the one ordinary solution lost at the lower end. If `d=K`, `W_K` ends
before `dec(10^K)`, so it is illegal and the deficit remains. Thus the two
endpoints are distinct integers but contribute the same word and alignment.

For completeness, the ordinary carry refinement of (4.2) is exact. For every
`0<=t<=d-1`, intersect (4.2) with

```text
n == 10^t-1 (mod 10^t),       n != 10^(t+1)-1 (mod 10^(t+1));
```

These disjoint conditions say exactly that `n` has `t` trailing nines and
partition every ordinary solution. Together with the single rollover class
they account for every exact carry type without an independence assumption.

Consequently, after summing those exact carry subclasses, the number of
high-stratum starts at `(d,a)` carrying `w` is

```text
h_(d,a)(w)=
  1[w_0!=0]10^(d-m),                         a=0;
  9*10^(d-m-1),                         1<=a<=d-m;
  1[w_(d-a)!=0]10^(d-m)
       -1[d=K and w=rho_(K,a)],          d-m<a<d.           (4.4)
```

Formula (4.2) uses the actual
successor, so no independence of carries is assumed. Refinement by `t` merely
partitions its ordinary solutions. Formula (4.4) includes every endpoint:
rollovers below `K` are present, while exactly the terminal rollovers are
removed.

Define

```text
A_(K,m)=sum_(d=m)^K 10^(d-m)=(10^(K-m+1)-1)/9,
B_(K,m)=(9/10)sum_(d=m)^K (d-m)10^(d-m),
Z(w)=#{j in {0,...,m-1}:w_j!=0},
R_(K,m)(w)=#{a in {K-m+1,...,K-1}:w=rho_(K,a)}.            (4.5)
```

`B_(K,m)` is an integer: its `d=m` summand vanishes and every later power is
divisible by ten. For each `d`, the `m` constrained leading digits in (4.4)
run once through `w_0,...,w_(m-1)`, while the `d-m` internal nonleading
alignments contribute the constant term.

The words `rho_(K,a)` are distinct (their initial runs of nines have distinct
positive lengths), so `R_(K,m)(w)` is `0` or `1` and
`sum_w R_(K,m)(w)=m-1`. Summing (4.4) over all high strata and alignments gives

```text
H_(K,m)(w)=A_(K,m)Z(w)+B_(K,m)-R_(K,m)(w).                (4.6)
```

## 5. Low strata and the exact multiplicity formula

Let `D_(K,m)(w)` count legal starts whose anchor stratum has `d(i)<m`.
Because `K>=m`, all starts before the end of `W_(m-1)` have endpoints inside
`W_K`; therefore

```text
sum_w D_(K,m)(w)=L_(m-1),
0<=D_(K,m)(w)<=L_(m-1).                                   (5.1)
```

These starts retain their full multi-boundary records from Section 3. Combining
(4.6) and (5.1) yields the exact formula

```text
c_(K,m)(w)=A_(K,m)Z(w)+B_(K,m)+D_(K,m)(w)-R_(K,m)(w).     (5.2)
```

Summing (5.2) over all words gives `M_(K,m)` independently, and also verifies
the endpoint identity

```text
M_(K,m)=10^m B_(K,m)+9m*10^(m-1)A_(K,m)
          +L_(m-1)-(m-1)=L_K-m+1.                         (5.3)
```

## 6. Centered energy identity

Let `U` be uniform on the `10^m` words and put

```text
mu=M_(K,m)/10^m,
X(w)=Z(w)-9m/10,
Y(w)=D_(K,m)(w)-R_(K,m)(w)
     -(L_(m-1)-(m-1))/10^m.                               (6.1)
```

Under `U`, `Z` is binomial with parameters `(m,9/10)`, hence

```text
sum_w X(w)=0,
sum_w X(w)^2=10^m*(9m/100).                               (6.2)
```

Equations (5.2)--(5.3) give

```text
c_(K,m)(w)-mu=A_(K,m)X(w)+Y(w),
sum_w Y(w)=0.                                              (6.3)
```

The general histogram identity now gives the exact centered pair formula

```text
E_(K,m)=M_(K,m)^2/10^m
         +sum_w (A_(K,m)X(w)+Y(w))^2.                     (6.4)
```

In particular the deviation is nonnegative. This is stronger than an
uncentered maximum-occupancy estimate and is where the first-order constant
becomes visible.

## 7. Explicit uniform error bound

Put `S=L_(m-1)+(m-1)`. Since `D,R>=0`, their total masses are `L_(m-1)` and
`m-1`; thus `|Y(w)|<=S` and

```text
sum_w Y(w)^2 <= 10^m S^2.                                 (7.1)
```

By Cauchy--Schwarz in (6.4),

```text
0 <= E_(K,m)/(M_(K,m)^2/10^m)-1
 <= [ (3/10)A_(K,m)*sqrt(m)+S ]^2 * 10^(2m)/M_(K,m)^2.    (7.2)
```

For `K>=4` and `m<=K/4`, the last stratum gives

```text
M_(K,m)>=8K*10^(K-1),                                     (7.3)
A_(K,m)<(10/9)10^(K-m),                                   (7.4)
S<=m*10^(m-1)+m <=2m*10^(m-1).                            (7.5)
```

Substitution into (7.2) gives the completely explicit uniform bound

```text
0 <= E_(K,m)/(M_(K,m)^2/10^m)-1
 <= epsilon_(K,m)
 := (1/(64K^2))*((10/3)*sqrt(m)+2m*10^(2m-K))^2.          (7.6)
```

Since `2m-K<=-K/2`, `m<=K/4`, and `K>=4`,
`2m*10^(2m-K)<=1/5`. Therefore also

```text
epsilon_(K,m)
 <= (1/(64K^2))*((5/3)*sqrt(K)+1/5)^2
 <= 1/(16K).                                               (7.7)
```

The last inequality follows from
`(5sqrt(K)/3+1/5)^2 <=4K`, valid for `K>=4` (divide by `K`, use
`1/sqrt(K)<=1/2` and `1/K<=1/4`, obtaining at most
`25/9+1/3+1/100<4`). Hence, uniformly for the entire growing-depth range,

```text
|E_(K,m)/(M_(K,m)^2/10^m)-1| <=1/(16K) -> 0.              (7.8)
```

This proves the requested
`E_(K,m)=(1+o(1))*M_(K,m)^2/10^m` with an explicit uniform error. No finite
calculation is used in Sections 4--7.

## 8. T160/T165 comparison and novelty boundary

Verification levels are essential.

| Comparator | What is available | Exact T169 boundary |
|---|---|---|
| T160, byte-exact `prior-T160-REPORT.md`, SHA-256 `94858ae03b2bad5ef66a0d46fa869c3f0dd3cd62d1cf076e7ae2c7104ca30b76` | Lines 5--10 label source statements `literature-checked`, deductions `proof sketch`, replay `experiment`, and the pi bridge unproved. Lines 213--261 identify ordered multiplicity through a sparse base-2 Champernowne lower bound, but give no base-10 upper asymptotic. | T169 imports no T160 claim. It gives exact base-10 high-stratum counts, centers all multiplicities, and proves a uniform first-order constant over every `1<=m<=K/4`. |
| T165, byte-exact `prior-T165-REPORT.md`, SHA-256 `a151ea4c939c65c48d3b728664ccc26b7eb0d7c7b2826b4babf1286c060384fc` | Lines 5--10 label its universal argument an unverified `proof sketch` and its replay an `experiment`. Lines 251--289 argue for `E/M^2<=15/(4*10^m)` by maximum occupancy; no first-order constant is proved. | T169 re-proves all definitions and counting it needs. Formula (4.4) replaces the deliberately coarse high-alignment cap by an exact leading-digit count and pairs each missing ordinary endpoint with its actual rollover below `K`; (6.4) replaces `E<=M*cmax` by exact centered variance. Thus T169's new content is the sharp `1+O(1/K)` asymptotic, not T165's upper bound. |

No global novelty claim is made. This table establishes only the required local
nonduplication against the named T160/T165 artifacts. In particular, the T165
note is not treated as a discharged premise.

## 9. Finite falsification replay (`experiment`, not proof)

From a directory containing only delivered artifacts, run

```bash
python3 verify_t169.py > replay.txt
diff -u raw_output.txt replay.txt
sha256sum -c SHA256SUMS
```

The verifier first authenticates the byte-exact comparator reports and their
label/claim anchors. It then constructs bounded `W_K`, enumerates every legal
start, builds the complete boundary/exact-carry/rollover record, reconstructs ordered energy from the
pair classes, and checks (4.4), (5.2)--(5.3), (6.2)--(6.4), and (7.2) on a
bounded grid. It also checks the canonical hash and report markers. These tests
can falsify endpoint or algebraic identities; finite replay is not evidence for
the universal proof.

## 10. Separate unproved transfer toward T7

**PI-PAIR-CLASS-CANCELLATION-T169 (`conjecture`; UNPROVED PI TRANSFER; NOT
ASSERTED).** Transfer toward the machine-checked T7 symbolic interface would
require an analogous theorem for the fixed decimal orbit of pi: for all
sufficiently large depths, on suitable pi prefixes, partition every ordered,
diagonal-inclusive equal-block pair into explicit arithmetic classes and prove
the required centered pair-class cancellation uniformly, without assuming the
desired collision, occupancy, discrepancy, or Fourier bound.

The Champernowne identity (4.2) comes from concatenating consecutive integers;
pi has no such successor structure. T169 proves no analogous theorem for pi
and makes no fixed-pi, A1, C1, or C2 claim.

## 11. Endpoint

`SCOPED VERDICT: SHARP RELATED-MODEL ASYMPTOTIC (proof sketch).`

The finite base-10 Champernowne prefixes satisfy (7.8), uniformly throughout
`1<=m<=floor(K/4)`. The claim remains a proof sketch pending independent
checking or formalization; replay is falsification only.
