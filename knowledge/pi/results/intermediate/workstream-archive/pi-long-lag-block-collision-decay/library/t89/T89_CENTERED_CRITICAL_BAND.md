# T89: the complete centered remainder in the critical band

Classification: `proof sketch`.

## 1. Verdict, provenance, and scope

This note gives terminal outcome 3 from the agenda: an exact strict
quantitative saving over the literal term-by-term triangle majorant, followed
by one displayed lower-dimensional fixed-`pi` correlation inequality that is
equivalent to the remaining target-scale gap. The saving is unconditional but
parameter-dependent; this note does not claim a scale-uniform proportional
saving.

The canonical local statement is included byte-for-byte as
`CANONICAL_STATEMENT.txt`. It has no external source URL. Its SHA-256 is

```text
db1a5656ab93808f9729f08a2e0cae8c7612d5d3225b41ca791f5f381d90a0c3
```

The canonical question concerns ordered nonoverlapping decimal-block
collisions. T89 concerns only T29's residual sparse-Fourier sibling A12. It
does not weaken, replace, prove, or refute the canonical question.

Fix an arbitrary `Q0 : Nat`. Simultaneously for every pair of positive
integers `m,N` satisfying

```text
H := 10^m,                 H <= N^2 <= 2H,                 (1.1)
```

we take

```text
(mu,c,alpha,s) = (8,1,pi,1/2),
Q(m,N) = H * (N + N^2/sqrt(H)).                            (1.2)
```

Here `Q(m,N)` is T29's literal outer inclusive-frequency factor times
`scaleMatchedTarget(1/2,m,N)`. The quantifier is over every positive critical-
band pair, not merely a selected sequence. The only interpretation choices
are these:

1. "Centered remainder" means the literal T29 observable minus T87's exact
   record diagonal.
2. A block endpoint has depth `d=N-B.finish`.
3. A termwise triangle bound is taken before any fixed-`pi` cancellation:
   every retained `(block,h,q,r)` with `q != r` is bounded by one.
4. An unordered two-core sum below means each pair of distinct cores occurs
   once.

The imported declarations listed next are `machine-checked`. The new
orientation quotient, cosine formulas, strict deficit, and final reduction in
this note are finite algebra checked in prose, so the combined result remains
a `proof sketch` under the program vocabulary. No novelty or
`literature-checked` claim is made.

## 2. Imported checked interfaces

The exact source hashes inspected for this note are

```text
T27FiniteExponentialCylinderCoverage.lean
  fd9c730e411dd7fb12b5b1a103c683238595c68bbea0f06af0250b4d13a8ee4e
T22SparseFrequencyCutoff.lean
  73b49990d59e2c446b121eee977a04b9bbb4806f7c47be01c384acb8bf7d1713
T29WidthWeightedSquareFunction.lean
  2f18966e04e00eb657d4a517d31281f9e8eafae4a6365bcf0985b94711e1e358
T32AllBlockFixedPiRange.lean
  3bb7e8a1fc13a87dd6decba4edd7dd1aa4daef51233b585e2e48e81bb2e78fdc
T49PrimitiveIncidenceAssembly.lean
  65776873b77b51df5639e7546db7319f14ce4b76259d3faa19732744e6e13cdb
T87RecordDiagonalCriticalBand.lean
  88b17a0be03261d3b53fe64d09452491920ca3550194d4bd2efa22f0ca2519e4
```

The following interfaces are used without re-derivation.

| Item | Checked declaration | Literal information retained |
|---|---|---|
| T27 | `phase` | The exact convention `exp(2*pi*i*h*x)` |
| T22 | `signedDecimalFrequency_injective_of_admissible` | Distinct admissible ordered records have distinct signed frequencies |
| T29 | `inclusiveFrequencies`, `mem_inclusiveFrequencies_iff` | Exactly `1 <= h <= 10^m`; zero is absent and `h=10^m` is present |
| T29 | `translatedCanonicalBlocks`, `translatedCanonicalBlock_spec` | T24's translated canonical binary blocks partitioning `[1,N)` |
| T29 | `canonicalBlockVector`, `blockSquaredEnergy`, `widthWeightedSquareFunction` | Every block vector, squared norm, and literal width-weighted block sum |
| T29 | `widthWeight_eq_endpoints` | `w_B=sqrt(B.finish^2-B.start^2)` |
| T32 | `mem_blockRecordDomain_iff` | Positive lag, `m <= r`, arithmetic survival, weak left endpoint, strict right endpoint |
| T32 | `blockRecordDomain_both_orientations` | Both Boolean orientations and their opposite nonzero signed frequencies |
| T32 | `blockSquaredEnergy_eq_diagonal_add_offDiagonal` | Every diagonal record pair contributes exactly `10^m` |
| T32 | `widthWeightedSquareFunction_eq_diagonal_add_offDiagonal` | Exact all-block diagonal plus ordered off-diagonal identity |
| T49 | `centeredWidthWeightedSquareFunction_eq_sectors` | Exact primitive plus cancelling partition of the complete centered term |
| T87 | `not_arithmeticExcluded_eight_one` | At `(mu,c)=(8,1)`, no admissible record is excluded, for every positive `m` and arbitrary `Q0` |
| T87 | `blockRecordDomain_both_orientations_eight_one`, `blockRecordDomain_card_eight_one` | Exact surviving domains, signs, orientations, and block cardinality |
| T87 | `recordDiagonal_exact_formula_literal` | Exact inclusive-frequency record diagonal with every block and width |
| T87 | `canonicalBlock_endpointDepth_spec`, `recordDiagonal_endpointDepth_decomposition` | Exact endpoint-depth range and width coordinates |
| T87 | `recordDiagonal_normalized_critical_bounds_literal` | The two explicit critical-band diagonal constants |

T87 imports T29 and the T32 record interfaces through its checked dependency
chain. No unverified T86 claim is used as a premise.

## 3. Exact domains, orientations, signs, and widths

Write T29's canonical block list as

```text
B in B_N := translatedCanonicalBlocks(N),
B = [a_B,b_B),             ell_B := b_B-a_B = 2^(B.level),
d_B := N-b_B,              w_B := sqrt(b_B^2-a_B^2).       (3.1)
```

For a core `p=(r,n)` define

```text
lambda_p := 10^n*(10^r-1),       E_p := n+r.               (3.2)
```

Before the T87 audit, the literal T32 core condition is

```text
0 < r,  m <= r,
not ArithmeticExcluded 8 1 Q0 m n r,
a_B <= E_p < b_B.                                         (3.3)
```

Thus no arithmetic exclusion has been silently omitted. Applying T87's
checked `not_arithmeticExcluded_eight_one` to (3.3) gives the exact unoriented
core domain

```text
P_B := {(r,n) in Nat^2 : 0 < r, m <= r,
                            a_B <= n+r < b_B}.             (3.4)
```

Both ordered orientations survive:

```text
Q_B := {false,true} x P_B,
sigma(false,p) = -lambda_p,
sigma(true,p)  = +lambda_p.                               (3.5)
```

Every record has coefficient one. Put `K_B=|P_B|` and `M_B=|Q_B|=2K_B`.
For later cardinality checks, define with natural-number subtraction

```text
Phi_m(K) := (K-m)*(K-m+1).                                (3.6)
```

T87 gives exactly

```text
M_B = Phi_m(b_B)-Phi_m(a_B)
    = 2 * sum_(E=a_B)^(b_B-1) max(E-m+1,0).               (3.7)
```

The depth theorem supplies, for every retained block and with no asymptotic
replacement,

```text
b_B = N-d_B,
a_B = N-d_B-ell_B,
0 <= d_B < ell_B,          d_B <= ell_B-1,
w_B = sqrt(ell_B*(2N-2d_B-ell_B)).                        (3.8)
```

In particular all denominators are the literal positive T29 widths.

## 4. Exact diagonal-plus-centered identity

For `1 <= h <= H` put

```text
theta_p(h) := 2*pi^2*h*lambda_p,
S_B(h) := sum_(p in P_B) cos(theta_p(h)).                 (4.1)
```

The normalization follows directly from T27's checked phase convention
`phase(h,x)=exp(2*pi*i*h*x)`: at `alpha=pi`, orientation `sigma` contributes
`exp(2*pi^2*i*h*sigma)`. Summing the two signs in (3.5) first gives

```text
sum_(q in Q_B) exp(2*pi^2*i*h*sigma(q)) = 2*S_B(h).       (4.2)
```

Consequently the literal full nonnegative T29 observable is

```text
W(m,N)
  = widthWeightedSquareFunction 8 1 Q0 m N pi
  = 4 * sum_(B in B_N) (1/w_B)
        * sum_(h=1)^H S_B(h)^2.                           (4.3)
```

T87's exact record diagonal is

```text
D(m,N)
  = recordDiagonal Q0 m N
  = H * sum_(B in B_N) M_B/w_B
  = 2H * sum_(B in B_N) K_B/w_B.                         (4.4)
```

Equivalently, its completely depth-expanded form is

```text
D(m,N) = H * sum_(B in B_N)
  [Phi_m(N-d_B)-Phi_m(N-d_B-ell_B)]
  / sqrt(ell_B*(2N-2d_B-ell_B)).                         (4.5)
```

Define the complete centered signed remainder, without an absolute value, by

```text
R(m,N) := W(m,N)-D(m,N).                                 (4.6)
```

Then (4.3)-(4.6) give the first exact requested identity:

```text
W(m,N) = D(m,N)+R(m,N),                                  (4.7)

R(m,N) = 4 * sum_(B in B_N) (1/w_B) * sum_(h=1)^H S_B(h)^2
         - 2H * sum_(B in B_N) K_B/w_B.                  (4.8)
```

This is also exactly T32's checked ordered off-diagonal sum:

```text
R(m,N) = sum_(B in B_N) (1/w_B)
  * sum_((q,r) in Q_B^2, q != r)
      sum_(h=1)^H exp(2*pi^2*i*h*(sigma(r)-sigma(q))).    (4.9)
```

Although (4.9) is written complexly, reversal `(q,r)<->(r,q)` shows it is
real. Equations (4.3), (4.8), and (4.9) are the same finite identity, not three
different observables.

## 5. Complete signed-sector audit

Define the real inclusive kernel for every positive integer `t` by

```text
C_H(t) := sum_(h=1)^H cos(2*pi^2*h*t).                    (5.1)
```

Expanding all signs in (4.9) partitions the remainder into exactly three
disjoint orientation/core sectors:

```text
R(m,N) = sum_(B in B_N) (1/w_B) * [
    2 * sum_(p in P_B) C_H(2*lambda_p)
  + 4 * sum_({p,p'} subset P_B, p != p')
        (C_H(|lambda_p-lambda_p'|)
         + C_H(lambda_p+lambda_p'))].                    (5.2)
```

The first line is the opposite-orientation pair attached to one core. For two
distinct cores, the difference kernel is the complete same-sign sector and
the sum kernel is the complete opposite-sign sector. The coefficients `2,4,4`
count all ordered record pairs in (4.9), including reversal. Every `C_H`
remains signed; no absolute value has entered (5.2).

For comparison with T85's terminology, the kernel-checked T49 partition is
also retained literally. Its positive-difference domain chooses exactly one
of each reversal pair by the strict signed-frequency order. It is the disjoint
union of

```text
primitive:  Noncancelling fourTokenSign(blockDifferenceExponent(p)),
cancelling: the complementary cancellingBlockDifferenceDomain.             (5.3)
```

T49's exact identity therefore reads

```text
R(m,N)
  = primitiveSectorContribution 8 1 Q0 m N pi
  + cancellingPositiveSectorContribution 8 1 Q0 m N pi,  (5.4)
```

where both displayed contributions carry T49's factor `2`, every canonical
block, every positive difference, every frequency in (5.1), and the divisor
`w_B`. Equations (5.2) and (5.4) are two exhaustive partitions of the same
remainder. Neither the primitive nor cancelling sector is discarded or
assumed nonnegative.

## 6. Exact endpoint-depth split

Let `F_B` denote the entire bracket in (5.2), including all three sectors.
For each integer `e` with `0 <= e < N`, define

```text
R_[e](m,N) := sum_(B in B_N, d_B=e)
  F_B / sqrt(ell_B*(2N-2e-ell_B)).                        (6.1)
```

If no canonical block has depth `e`, this sum is zero. Since every block has
`b_B>=1`, its depth is below `N`; since T87 gives `d_B<ell_B`, the exact split
and its per-block range are

```text
R(m,N) = sum_(e=0)^(N-1) R_[e](m,N),
R_[e] can contain B only when 0 <= e <= ell_B-1.          (6.2)
```

For every arbitrary depth cutoff `q`, including `q>=N`, (6.2) also gives the
literal two-part split

```text
R(m,N) = R_depth<=q(m,N) + R_depth>q(m,N),               (6.3)

R_depth<=q := sum_(0<=e<N, e<=q) R_[e],
R_depth>q  := sum_(0<=e<N, q<e)  R_[e].                  (6.4)
```

This is a split of the full signed remainder, not a bound. Separately, T87's
checked terminal-suffix estimate filters blocks by `ell_B<=2^q` and controls
only the corresponding diagonal mass. If
`(N-1).bitIndices.reverse=j0::js`, its exact constant is

```text
D_length<=2^q := H * sum_(B in B_N, ell_B<=2^q) M_B/w_B,

D_length<=2^q / D
  <= [32*(2+sqrt(2))/9] * sqrt(2^q/2^j0).                (6.5)
```

No use of (6.5) is made to bound either signed term in (6.3).

## 7. Terminal outcome 3: strict triangle saving

For each block let `U_B` contain one representative of every unordered pair
of distinct signed records in `Q_B`. Concretely, choose the representative
`(q,r)` with `sigma(r)<sigma(q)`, and put

```text
delta(q,r) := sigma(q)-sigma(r) > 0,
|U_B| = M_B*(M_B-1)/2.                                  (7.1)
```

T22's checked injectivity of signed decimal frequency on admissible records
ensures that this strict ordering loses no off-diagonal pair. Reversal in
(4.9) gives the exact real quotient

```text
R(m,N) = 2 * sum_(B in B_N) (1/w_B)
                   * sum_(u in U_B) C_H(delta(u)).        (7.2)
```

The literal phase-by-phase termwise triangle majorant is therefore

```text
T_tri(m,N)
  := H * sum_(B in B_N) M_B*(M_B-1)/w_B
   = 2H * sum_(B in B_N) |U_B|/w_B.                      (7.3)
```

This retains, rather than globally replacing, each exact block cardinal and
width. To quantify the strict improvement, set

```text
Delta_pair(m,N) := 2 * sum_(B in B_N) (1/w_B)
  * sum_(u in U_B) [H-|C_H(delta(u))|].                  (7.4)
```

For positive integers `h,t`,

```text
|cos(2*pi^2*h*t)| < 1.                                  (7.5)
```

Indeed equality would make `2*pi*h*t` an integer and hence make `pi`
rational, contradicting the standard theorem `irrational_pi` (available in
the checked mathlib environment). This irrationality input is additional to
the T29/T32/T49/T87 interfaces, and its use is explicit here. Thus
`|C_H(t)|<H` for every positive integer `t`. The critical lower bound implies
`4m<=N` by T87. Hence the core `(r,n)=(m,0)` has strict endpoint `m<N`, belongs
to one canonical block, and supplies its two distinct orientations. Therefore
at least one `U_B` is nonempty. All widths are positive, so

```text
Delta_pair(m,N) > 0,
|R(m,N)| <= T_tri(m,N)-Delta_pair(m,N) < T_tri(m,N).      (7.6)
```

This is already an exact additive quantitative saving. A proportional form
can also be audited. Let

```text
epsilon_*(m,N) := min_(B in B_N, u in U_B)
  [1-|cos(2*pi^2*delta(u))|].                            (7.7)
```

The indexing set is finite and nonempty, and (7.5) gives `epsilon_*>0`.
Using the `h=1` term separately gives

```text
|C_H(delta(u))| <= H-epsilon_*(m,N),
|R(m,N)| <= (1-epsilon_*(m,N)/H)*T_tri(m,N).              (7.8)
```

The factor in (7.8) is explicit and strictly below one for every positive
critical-band pair. No lower bound for `epsilon_*` uniform in `m,N` is proved
or asserted. In particular, T87's arithmetic-exclusion audit is not such a
fixed-`pi` separation estimate.

## 8. The one remaining lower-dimensional correlation inequality

The four sign choices can be combined more strongly than reversal pairing.
Using (4.3), (4.4), and (7.3) gives the exact alignment-defect identity

```text
R(m,N) = T_tri(m,N)-Delta_align(m,N),                    (8.1)

Delta_align(m,N) := 4 * sum_(B in B_N) (1/w_B)
  * sum_(h=1)^H [K_B^2-S_B(h)^2].                        (8.2)
```

Each bracket in (8.2) is nonnegative because `|S_B(h)|<=K_B`; it is strict on
every nonempty block by (7.5). This identity removes the Boolean orientation
coordinate and the ordered pair of records. What remains is one real
correlation of the two integer core coordinates `(r,n)` at each `h`.

The entire unresolved target-scale gap is now the following single displayed
fixed-`pi` inequality, with all constants and quantifiers explicit:

```text
For every Q0 in Nat and all positive m,N with 10^m <= N^2 <= 2*10^m,

  4 * sum_(B in translatedCanonicalBlocks(N))
        1/sqrt(ell_B*(2N-2d_B-ell_B))
        * sum_(h=1)^(10^m)
            [K_B^2
             -(sum_((r,n) in P_B)
                 cos(2*pi^2*h*10^n*(10^r-1)))^2]

  >= T_tri(m,N)-10^m*(N+N^2/sqrt(10^m)).                (CORR_pi)
```

Here `P_B` is exactly (3.4), `0<=d_B<ell_B` exactly as in (3.8), and
`T_tri` is exactly (7.3). The apparent `Q0` is harmless only because T87 has
already proved that all exclusions vanish at `(8,1)`.

By (8.1), `(CORR_pi)` is equivalent to the one-sided centered estimate

```text
R(m,N) <= Q(m,N).                                        (8.3)
```

It is not proved here. It is the precise remaining fixed-`pi` input, not a
hidden assumption used in the strict saving. For completeness, T87's full
checked two-sided critical-band diagonal estimate is

```text
9/[16*(1+sqrt(2))] <= D(m,N)/Q(m,N)
                    <= 3/4+sqrt(2)/2.                    (8.4)
```

If `(CORR_pi)` is later proved, the upper half of (8.4) and (4.7) immediately
give the fully explicit conditional consequence

```text
W(m,N)/Q(m,N) <= 7/4+sqrt(2)/2 < 5/2.                   (8.5)
```

Thus T89 does not replace the fixed-`pi` problem by a qualitative phrase such
as "some cancellation": it identifies the exact finite correlation and the
constant needed after the diagonal has been removed.

## 9. T85 is heuristic motivation only

The source files used for this paragraph have hashes

```text
T85 REPLAY.md
  421d1d304c7ed7da61e9a7fa34eb4d80c29e76c2affa2cbd2a46cf12d11447ff
T85 results.json
  2f7baabf87783601a8361f9041c214cb30e5d31a8c1cf1cd9780a3966791f2cf
```

T85 is classified as an `experiment`. Of its fifteen evaluated points, the
four transition cases lie in the present critical band. Their certified full-
observable ratios to (1.2) are approximately

```text
(m,N)=(2,11):  0.5094242695
(m,N)=(3,33):  0.3847793851
(m,N)=(4,101): 0.7486593445
(m,N)=(5,317): 0.9331530813.                             (9.1)
```

The `(5,317)` mass is spread over all five canonical blocks, and T85 reports
signed primitive and cancelling sectors of changing sign. This motivates
retaining the full observable, every block, and both sectors. These are finite
heuristic observations only. They do not prove `(CORR_pi)`, any uniform
constant, or any universal claim, and they neither prove nor refute C2, C1,
or C3.

## 10. Exact conclusion and non-claims

The terminal outcome is the strict saving (7.6), strengthened by the explicit
proportional form (7.8), together with the reduction of the remaining
target-scale question to `(CORR_pi)`. The exact diagonal-plus-centered identity
is (4.7)-(4.9); all signed sectors are exposed in (5.2) and preserved again in
T49 form in (5.4); the exact endpoint-depth split and range are (6.1)-(6.4).

This note is a `proof sketch`, not a `machine-checked` T89 result. It gives no
conclusion for full C2, full C1, full C3, or the canonical collision count. It
does not exhibit an unbounded counterfamily and does not claim the target-scale
bound, because `(CORR_pi)` remains open.
