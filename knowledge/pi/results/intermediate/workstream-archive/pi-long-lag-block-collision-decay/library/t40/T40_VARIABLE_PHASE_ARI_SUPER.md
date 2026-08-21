# T40: variable-phase sibling of `ARI_super(36/5)`

Status: `proof sketch` with one terminal conjectural maximal-tail inequality.

This note does not assert T36's fixed-`pi` predicate, C3, C2, C1, or the
canonical collision estimate. Every conclusion below concerns only the
variable-phase sibling obtained by replacing `Real.pi` in T36's shell phases
by a Lebesgue-random real `alpha`.

## 1. Provenance and statement normalization

The canonical local problem has no external source URL. A byte-exact copy is
delivered as `CANONICAL_STATEMENT.txt`; its verified SHA-256 is

```text
db1a5656ab93808f9729f08a2e0cae8c7612d5d3225b41ca791f5f381d90a0c3.
```

The canonical problem asks about the decimal collision count at `pi`. T40
does not estimate that count. It stress-tests the variable-phase sibling of
T36's residual sparse-Fourier incidence predicate.

Fix arbitrary natural numbers `Q0,Qstar`. They are parameters fixed before
the exponent, scale variables, blocks, and row parameters. No positivity
assumption on either is added. The sibling to be decided is

```text
for phaseMeasure-almost every alpha,
  for every real s with 0 < s < 1,
    there exists a real C = C(Q0,Qstar,alpha,s) >= 0 such that
      for every natural m,N with 1 <= m and 1 <= N,

        X(Q0,Qstar;m,N;alpha)
          <= C [N + N^2 10^(-s m)].                       (1.1)
```

The constant may depend on the two fixed onset parameters, `alpha`, and `s`.
It may not depend on `m`, `N`, a block, a row, a shell, or any row parameter.

### Ambiguities explicitly resolved

1. `alpha` replaces `pi` only in the shell tests. All six row domains and all
   arithmetic-survival predicates remain T36's literal ones at `(mu,c)=(8,1)`.
2. The probability space is the half-open unit interval with the restricted
   Lebesgue measure defined in Section 5. No probability law on decimal digit
   sequences is introduced.
3. The almost-everywhere quantifier precedes the uncountable `for every s`.
   Section 9 handles this point using a countable cofinal sequence of exponents.
4. Both terms `N` and `N^2 10^(-s m)` are retained.
5. Shell zero and every positive shell retain T34's open/closed endpoints.
6. This note does not use T37 as a premise. It also does not use any claim from
   the unverified T39 note.

## 2. Machine-checked definitions reused

The definitions transcribed below come from these accumulated kernel-checked
files. Their hashes were rechecked in the T40 sandbox.

```text
T8SpectralLongLagReduction.lean
  f0c71d2ca404c69f11617f4ddf7587fcc814c897954cf70936a55d8d603f9ee9
T22SparseFrequencyCutoff.lean
  73b49990d59e2c446b121eee977a04b9bbb4806f7c47be01c384acb8bf7d1713
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

The new claims in Sections 6-9 are prose derivations, not Lean theorems and
not `machine-checked` declarations.

## 3. Exact records, six rows, and survival domains

A long-pair core is `(r,n)` with lag `r` and smaller start `n`. An ordered
record is

```text
q = (epsilon,(r,n)), epsilon in {false,true}.
```

Its endpoint is `E(q)=n+r`. For an orientation, start, and endpoint, T34 uses

```text
record(epsilon,n,E) = (epsilon,(E-n,n)),                    (3.1)
```

where subtraction is natural subtraction. A malformed endpoint order gives
lag zero and is rejected below; it is not silently admitted.

For positive `r`, put

```text
qden(n,r) = 10^n(10^r-1),

ArithmeticExcluded(8,1,Q0,m,n,r) iff
  Q0 <= qden(n,r) and
  10^(-m) <= qden(n,r) [1 / qden(n,r)^8].                  (3.2)
```

All powers and inequalities in the second line are over the reals. The exact
block record domain is

```text
q in blockRecordDomain(8,1,Q0,m,B) iff
  0 < r,
  m <= r,
  not ArithmeticExcluded(8,1,Q0,m,n,r),
  B.start <= n+r < B.finish.                               (3.3)
```

Thus (3.3) retains the weak long-lag cutoff, strict block endpoint, both Bool
orientations, and the exact arithmetic exclusion.

The outer repunit parameter domain is

```text
D_N = {(v,rho): v<N, rho<N, 0<rho, v+rho<N}.               (3.4)
```

Write

```text
k = v+rho,
d(v,rho) = 10^v(10^rho-1) = 10^k-10^v.                    (3.5)
```

Every `d(v,rho)` in (3.4) is a positive integer. T36's exact supercritical
filter is

```text
P(Qstar,m;v,rho) iff
  Qstar <= d(v,rho) and 5m < 31(v+rho).                    (3.6)
```

For every `z` in `range N`, the six T34 rows are the following ordered pairs
of records:

```text
row 1 positiveSameEndpoint:
  (record(true,k,z),  record(true,v,z));

row 2 positiveSameStart:
  (record(true,z,v),  record(true,z,k));

row 3 negativeSameEndpoint:
  (record(false,v,z), record(false,k,z));

row 4 negativeSameStart:
  (record(false,z,k), record(false,z,v));

row 5 mixedFirstEndpoint:
  (record(false,z,k), record(true,v,z));

row 6 mixedSecondEndpoint:
  (record(false,v,z), record(true,z,k)).                    (3.7)
```

For each named row, T34's `cancellingRowDomain` is the singleton containing
the displayed record pair, filtered by `rho>0` and membership of both records
in (3.3). Its cardinality is therefore exactly zero or one. No row has been
discarded or merged.

For a canonical block `B`, define the literal six-row hidden-exponent
multiplicity

```text
M_B(Q0,m,N;v,rho)
  = sum_{0<=z<N} sum_{row in the six rows}
      card(cancellingRowDomain(8,1,Q0,m,B,row,v,rho,z)).     (3.8)
```

## 4. Canonical blocks and literal width

A dyadic block is a pair `(a,j)` representing

```text
B.start = a,
B.blockLength = 2^j,
B.finish = a+2^j.                                          (4.1)
```

T24's recursive `dyadicPartitionFrom(q,js)` starts its first block at `q+1`
and advances `q` by the preceding block length. The exact canonical list is

```text
B_N = translatedCanonicalBlocks(N)
    = dyadicPartitionFrom(0,(N-1).bitIndices.reverse).      (4.2)
```

It is a consecutive, nonduplicated partition of the integer endpoints
`[1,N)`. Every block in it satisfies `1<=B.start<B.finish<=N`. Its literal
weight is

```text
w_B = sqrt(B.finish^2-B.start^2).                           (4.3)
```

In particular, `w_B>=1`; no asymptotic replacement for (4.3) is made.

## 5. Probability space and exact endpoint-pinned shells

Let

```text
Omega = [0,1),
phaseMeasure = Lebesgue measure restricted to Omega.       (5.1)
```

This is T18/T31's probability measure and has total mass one. For real `x`,
put

```text
delta(x) = |x-round(x)|,
H_m = 10^m,
K_m = clog_2(H_m)-1.                                       (5.2)
```

For every positive `m`, T34 proves

```text
1 <= K_m,
H_m <= 2^(K_m+1),
2^K_m < H_m.                                               (5.3)
```

The shell predicates are exactly

```text
S_0(m,x): 0 <= delta(x) <= 1/H_m,

S_j(m,x): 2^(j-1)/H_m < delta(x)
            <= min(2^j/H_m,1/2),  1<=j<=K_m.              (5.4)
```

Define the literal shell weight

```text
theta_m(x)
  = 1_{S_0(m,x)}
      + sum_{j=1}^{K_m} 2^(-j) 1_{S_j(m,x)}.               (5.5)
```

Shell zero is closed at both ends. Every positive shell is open below and
closed above, including the terminal cap at `1/2`. Formula (5.5), rather than
an equivalent almost-everywhere modification, is used in the incidence.

## 6. Exact variable-phase incidence

For `j=0,...,K_m`, define

```text
I_j(Q0,Qstar;m,N;alpha)
  = sum_{B in B_N}
      sum_{(v,rho) in D_N; P(Qstar,m;v,rho)}
        if S_j(m,d(v,rho) alpha) then M_B(Q0,m,N;v,rho)/w_B
        else 0.                                             (6.1)
```

The T40 random variable is

```text
X(Q0,Qstar;m,N;alpha)
  = I_0(Q0,Qstar;m,N;alpha)
      + sum_{j=1}^{K_m} 2^(-j) I_j(Q0,Qstar;m,N;alpha).     (6.2)
```

Comparing (6.1)-(6.2) with T36's `restrictedShellIncidence` and
`restrictedWeightedShellIncidence`, the only changed token with mathematical
content is

```text
d(v,rho) * Real.pi   replaced by   d(v,rho) * alpha.       (6.3)
```

All finite sums, filters, multiplicities, weights, shell endpoints, and onset
conditions are unchanged.

Because all sums are finite, distributivity gives the exact direct identity

```text
X(Q0,Qstar;m,N;alpha)
  = sum_{B in B_N}
      sum_{(v,rho) in D_N; P(Qstar,m;v,rho)}
        [M_B(Q0,m,N;v,rho)/w_B]
        theta_m(d(v,rho) alpha).                            (6.4)
```

No limiting rearrangement is used. Every term is nonnegative. Each shell set
is Borel measurable, so (6.1), (6.2), and every finite maximum used below are
measurable functions of `alpha`.

## 7. Exact shell measures

For `1<=j<=K_m`, set

```text
ell_(m,j) = 2^(j-1)/H_m,
u_(m,j)   = min(2^j/H_m,1/2).                              (7.1)
```

### Lemma 7.1: multiplication by a positive integer

For every positive integer `d`, every positive `m`, and every
`1<=j<=K_m`,

```text
phaseMeasure{alpha: S_0(m,d alpha)} = 2/H_m,               (7.2)

phaseMeasure{alpha: S_j(m,d alpha)}
  = 2[u_(m,j)-ell_(m,j)].                                  (7.3)
```

#### Proof-sketch derivation

Partition `[0,1)` into the `d` half-open intervals
`[r/d,(r+1)/d)`, `0<=r<d`, and on the `r`th interval put
`t=d alpha-r`. The Jacobian is `1/d`, and `t` traverses `[0,1)`.
Translation by the integer `r` does not change distance to the nearest
integer. Summing the `d` identical branch integrals shows that
`delta(d alpha)` has the same distribution as `delta(t)` for uniform
`t in [0,1)`.

For `0<=a<b<=1/2`, the set

```text
{t in [0,1): a < delta(t) <= b}
```

is, up to its finitely many endpoints, `(a,b] union [1-b,1-a)` and has
measure `2(b-a)`. Likewise `{delta(t)<=b}` has measure `2b`. Here
`1/H_m<1/2`. Also (5.3) implies `ell_(m,j)<1/2`, so (7.2)-(7.3) follow with
the literal open/closed conventions. Endpoints have measure zero, but the
sets in (7.2)-(7.3) are exactly the sets from (5.4).

### Corollary 7.2: exact first shell moment

For every positive integer `d`,

```text
integral_Omega theta_m(d alpha) d alpha = kappa_m,          (7.4)

kappa_m
  = 2/H_m
      + sum_{j=1}^{K_m} 2^(-j)
          2[min(2^j/H_m,1/2)-2^(j-1)/H_m].                (7.5)
```

In particular, the integral is independent of `d`. Moreover,

```text
0 <= kappa_m <= (K_m+2)/H_m <= 5m/H_m.                    (7.6)
```

Indeed, every positive-shell summand in (7.5) is at most `1/H_m`, giving the
first upper bound. Since `10^m<=16^m=2^(4m)`, the least-exponent definition of
`clog` gives `K_m+2<=4m+1<=5m` for `m>=1`.

## 8. Exact first moment and its limitation

Define the deterministic supercritical mass

```text
A(Q0,Qstar;m,N)
  = sum_{B in B_N}
      sum_{(v,rho) in D_N; P(Qstar,m;v,rho)}
        M_B(Q0,m,N;v,rho)/w_B.                             (8.1)
```

Every coefficient `d(v,rho)` in (8.1) is positive. Finite linearity of the
integral, (6.4), and (7.4) therefore give the exact finite identity

```text
integral_Omega X(Q0,Qstar;m,N;alpha) d alpha
  = kappa_m A(Q0,Qstar;m,N).                               (8.2)
```

This identity retains all six rows through `M_B`, every canonical block and
literal width through (8.1), and the exact supercritical filter.

For scale only, T36's machine-checked
`blockRepunitMultiplicity_block_sum_le` gives

```text
sum_{B in B_N} M_B(Q0,m,N;v,rho) <= 6N.                   (8.3)
```

Since `w_B>=1` and `card(D_N)<=N^2`, (8.1), (8.3), and (7.6) imply the coarse
but fully explicit estimate

```text
A(Q0,Qstar;m,N) <= 6N^3,

integral_Omega X(Q0,Qstar;m,N;alpha) d alpha
  <= 30m N^3 10^(-m).                                     (8.4)
```

Estimate (8.4) is not claimed to prove (1.1): applying Markov separately to
all pairs `(m,N)` does not give a summable bound uniform in `N`. The remaining
obstruction is genuinely maximal in the two scale variables.

## 9. One terminal maximal-tail inequality

For a real `s` and positive `m,N`, define the literal target

```text
T_s(m,N) = N + N^2 10^(-s m).                              (9.1)
```

It is strictly positive. For an integer `ell>=2`, put

```text
s_ell = 1-1/ell.                                           (9.2)
```

For `R>=1`, define the finite normalized maximum

```text
Z_(ell,R)(alpha)
  = max_{1<=m<=R, 1<=N<=R}
      X(Q0,Qstar;m,N;alpha) / T_(s_ell)(m,N).              (9.3)
```

Here is the single remaining probabilistic input.

```text
(MT)

For every fixed natural Q0,Qstar and every integer ell>=2,
there exists a finite real A_(Q0,Qstar,ell)>=0 such that,
for every real L>=1 and every integer R>=1,

  phaseMeasure{alpha in [0,1): Z_(ell,R)(alpha)>L}
    <= A_(Q0,Qstar,ell) / L.                               (9.4)
```

Statement `(MT)` is a `conjecture` in this note. It is not inferred from the
first moment (8.2) or from T31. It is one uniform weak-`L1` maximal-tail
inequality: its constant precedes both the cutoff `R` and tail level `L`.

### Proposition 9.1: `(MT)` decides the positive verdict

Assume `(MT)`. Then (1.1) holds for phaseMeasure-almost every `alpha`, with
one common full-measure set on which it holds for every real `0<s<1`.

#### Proof-sketch derivation

Fix `Q0,Qstar,ell`. For fixed `L`, the events in (9.4) increase with `R`.
Continuity from below and the uniformity in `R` give

```text
phaseMeasure{alpha: sup_{m,N>=1}
    X(Q0,Qstar;m,N;alpha)/T_(s_ell)(m,N) > L}
  <= A_(Q0,Qstar,ell)/L.                                  (9.5)
```

The event on which this supremum is infinite is contained in the event in
(9.5) for every positive integer `L`. Letting `L` tend to infinity shows that
the infinite-supremum event has measure zero. Thus, outside a null set
`E_ell`,

```text
C_(alpha,ell)
  = sup_{m,N>=1} X(Q0,Qstar;m,N;alpha)/T_(s_ell)(m,N)      (9.6)
```

is a finite nonnegative real and controls every positive `m,N`.

The union `E=union_{ell>=2} E_ell` is null. Fix `alpha` outside `E` and an
arbitrary real `s` with `0<s<1`. Choose `ell>=2` with

```text
s < s_ell < 1.                                             (9.7)
```

Because the base ten is greater than one, (9.7) gives

```text
10^(-s_ell m) <= 10^(-s m),
T_(s_ell)(m,N) <= T_s(m,N).                                (9.8)
```

Consequently (9.6), with `C=C_(alpha,ell)`, implies (1.1) for this `s` and
all positive `m,N`. This proves the claimed quantifier order: one full-measure
set first, then every real `s`, then a constant, then every positive `m,N`.

## 10. Verdict and claim boundary

**Variable-phase sibling: unresolved, reduced to `(MT)`.** The exact finite
variable-phase incidence is (6.1)-(6.2), its direct identity is (6.4), every
shell measure is (7.2)-(7.3), and its exact first moment is (8.2). The only
undischarged input in the positive almost-everywhere argument is the uniform
maximal-tail inequality `(MT)` in (9.4).

No almost-everywhere refutation was found. The coarse first moment (8.4) is
insufficient in the `N` direction and is not presented as evidence that
`(MT)` holds or fails. No conclusion is specialized to `pi`.

In particular, this note asserts no status for C3, C2, or C1 and no result
about the canonical collision count. T37 is not an established premise and
is not used.

## 11. Verification map

1. Canonical statement: `CANONICAL_STATEMENT.txt`, byte-verified hash in
   Section 1.
2. Fixed domains and weights: Sections 2-5, transcribed from the listed
   machine-checked T8/T22/T24/T29/T31/T32/T34/T36 interfaces.
3. Variable substitution audit: (6.1)-(6.3).
4. Exact finite direct identity: (6.4), finite distributivity only.
5. Measure, shell endpoints, and exact shell measures: (5.1)-(5.5) and
   Lemma 7.1.
6. Exact first moment and explicit constants: (7.4)-(8.4).
7. Full quantifier order and uncountable-`s` issue: (9.2)-(9.8).
8. Sole unresolved input: `(MT)`, explicitly labeled `conjecture`.
9. Lean declarations introduced: none.
10. Literature claims introduced: none.
11. Independent statement and proof review: pending.
