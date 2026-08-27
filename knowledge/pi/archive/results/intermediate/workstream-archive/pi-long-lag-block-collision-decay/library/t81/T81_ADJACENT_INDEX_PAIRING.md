# T81: adjacent-index pairing is additive, not cancelling

Claim label: `machine-checked` for the declarations listed in Section 9. The
displayed finite regroupings are direct readings of those declarations and the
imported T69/T76 interfaces. T80 is used only as unverified motivation.

Date: 2026-08-06 UTC.

## 1. Provenance, normalized statement, and scope

The canonical question is the locally formulated statement
`CANONICAL_STATEMENT.txt`; it has no external source URL. Its SHA-256 is

```text
db1a5656ab93808f9729f08a2e0cae8c7612d5d3225b41ca791f5f381d90a0c3
```

It asks whether, for every real `s` with `0<s<1`, one constant `C_s>=1`
works simultaneously for all positive integers `m,N` in the ordered
long-lag collision estimate

```text
R_pi(m,N) <= C_s*(N+N^2*10^(-s*m)).
```

T81 does not answer or alter that question. It concerns only T69's
residual-A12, `m=1`, dyadic primitive-sector sibling. The exact scale is

```text
N=N_t=4*2^t+1,
H=H_t=ceil(sqrt(N_t)).
```

The canonical ambiguities relevant here are explicit: this is not fixed `m`
evidence for A1, not an almost-everywhere phase statement, not a favorable
subsequence result for the canonical collision count, and not a result with a
constant allowed to depend on `m,N`. It is a quantitative refutation of one
proposed cancellation mechanism inside the A12 sibling.

The formal artifact imports, rather than duplicates,

```lean
import TheoryLib.PiLongLagBlockCollisionDecay.T69T69AggregateShiftHalfArc
import TheoryLib.PiLongLagBlockCollisionDecay.T76T76VariablePhasePooledHalfArc
```

The exact imported source SHA-256 values are

```text
T69: 09086eff08c0c09eefe02979107026fb3f19019887767b72d582ea0580e18301
T76: 7e8c65c5dcae4232da496646e7e9778f5aaf8067feb18875beb04c0d6b794fe7
```

The T80 note, SHA-256
`4d422c17fb22b2d24ba934ca667ab7e43508a4bcb8ae96158cf5c7ada024caa1`,
is an unverified `proof sketch`. It motivates avoiding positive unsigned
Cauchy majorants, but no T80 claim is a premise of T81.

## 2. Literal T69 signed expression and target

Write

```text
e(x)       = exp(2*pi*i*x),
f_r        = 10^r-1,
w_r        = H-r,
L_r        = N-r.
```

T69's kernel-checked `aggregateEnergy_literal` gives

```text
A_t(pi)
  = sum_(h=1)^10 sum_(r=1)^(H-1) w_r
      sum_(k=0)^(L_r-1) e(h*f_r*10^k*pi),               (2.1)

aggregateEnergy(t) = 10*H*N + 2*Re A_t(pi).             (2.2)
```

Thus the literal domains are

```text
1 <= h <= 10,
1 <= r < H,
0 <= k < N-r,
weight H-r.                                              (2.3)
```

Every term in (2.1) has a displayed plus sign. No absolute value, triangle
inequality, or Cauchy estimate has been applied. The one-sided T69 target is

```text
Re A_t(pi) <= C*H*N                                      (2.4)
```

for one scale-independent `C`; the stronger absolute-value version is not
needed here. Comparing coefficient mass with `H*N` below does not assert a
lower bound for `Re A_t(pi)` or `|A_t(pi)|`.

For `C>=0`, (2.2)--(2.4) would give T69's aggregate hypothesis with the exact
normalization

```text
K=10+2*C.                                                (2.5)
```

T69's kernel-checked `literal_aggregate_implies_primitiveBudget` would then,
for every `Q0,t` and every `0<s<1`, give its specialized selected-plus-defect
budget with right side

```text
10*((45/16)*K^2+5)*(N_t+N_t^2*10^(-s)).                (2.6)
```

Equations (2.5)--(2.6) only identify the target and its checked conditional
consequence. T81 supplies no `C` satisfying (2.4).

## 3. Exhaustive equal-frequency classes

T76's kernel-checked `pooledFrequency_eq_iff` says, throughout the complete
positive domain, that

```text
h*f_r*10^k = h'*f_s*10^l
```

holds exactly when `r=s` and one of the following occurs:

```text
(h',l)=(h,k),
(h,h',k)=(1,10,l+1),
(h,h',l)=(10,1,k+1).                                    (3.1)
```

The finite-domain form `literal_T69_frequencyClass_iff` retains
`k,l<N-r` and exposes the two endpoint failures. T81's
`equalFrequencyClass_exact` imports that classification at a general finite
length `L`. In particular, there are no equal-frequency collisions between
different shifts `r`, nor any nontrivial equal-frequency classes involving
`h=2,...,9`.

The only nontrivial identity is therefore

```text
10*f_r*10^k = f_r*10^(k+1).                             (3.2)
```

T81's `adjacentFrequency_eq` checks (3.2).

## 4. Pairing involution, signs, and boundaries

Fix `r` and put `L=L_r=N-r`. The interior pair domain is

```text
D_r = {(10,k): 0<=k and k+1<L}
      union {(1,j): 1<=j and j<L}.                       (4.1)
```

Define

```text
iota(10,k) = (1,k+1),
iota(1,j)  = (10,j-1).                                  (4.2)
```

The machine-checked theorems `adjacentSwap_mem`,
`adjacentSwap_involutive`, and `adjacentSwap_ne` prove respectively that
`iota` preserves (4.1), is an involution there, and has no fixed points.

Both terms of a pair have coefficient `+w_r`. The theorems
`adjacentTerms_equal`, `adjacentTerms_add`, and
`adjacentCoefficient_pos` give, for `r<H`,

```text
w_r*e(10*f_r*10^k*alpha)
  + w_r*e(f_r*10^(k+1)*alpha)
  = 2*w_r*e(f_r*10^(k+1)*alpha),

2*w_r > 0.                                               (4.3)
```

Hence equal-frequency pairing doubles the positive coefficient. It does not
cancel it.

There are exactly two boundary fibers for each `r`:

```text
(h,k)=(1,0),       coefficient +w_r, frequency f_r;
(h,k)=(10,L-1),    coefficient +w_r, frequency f_r*10^L. (4.4)
```

Theorems `leftBoundary_frequencyClass` and
`rightBoundary_frequencyClass` prove that each is a singleton frequency class
inside `0<=k<L`. Combining (4.3)--(4.4), the complete `h=1,10` part at shift
`r` is exactly

```text
w_r*[e(f_r*alpha)
     + 2*sum_(j=1)^(L-1) e(f_r*10^j*alpha)
     + e(f_r*10^L*alpha)].                               (4.5)
```

The full expression (2.1) is (4.5), summed over `1<=r<H`, plus the unchanged
terms

```text
sum_(r=1)^(H-1) w_r sum_(h=2)^9 sum_(k=0)^(L_r-1)
  e(h*f_r*10^k*pi).                                      (4.6)
```

Thus frequencies `1` through `10`, every triangular weight, and every orbit
endpoint remain present.

## 5. Unequal cutoffs and signed double expansion

For shifts `r,r'`, simultaneous activity at one orbit index is exactly

```text
k<N-r and k<N-r'
  iff k<N-max(r,r').                                     (5.1)
```

T81's `unequalCutoff_iff` checks (5.1). Consequently, if the sum is regrouped
as `A_t(alpha)=sum_(k=0)^(N-2) B_k(alpha)` and the exact same-`k` square is
expanded, its ordered `(h,r),(h',r')` term is

```text
w_r*w_r' * sum_(k=0)^(N-max(r,r')-1)
  e((h*f_r-h'*f_r')*10^k*alpha).                         (5.2)
```

Equation (5.2) is signed: reversing the ordered channel pair negates the
integer frequency and conjugates the sum. No termwise modulus is inserted.
The cutoff is not replaced by `N-r`, `N-r'`, or `N`. This exact identity is
recorded only to audit the unequal endpoints; T81's quantitative exit uses
the original linear expression (2.1), not an unsigned square estimate.

## 6. Explicit coefficient family

The interior pairs in (4.1) provide `L_r-1=N-r-1` equal-frequency pairs at
shift `r`. Their total coefficient mass is therefore

```text
M_t = 2*sum_(r=1)^(H-1) (H-r)*(N-r-1).                  (6.1)
```

This is an actual family of coefficients in (2.1), not a finite numerical
sample. T76's exhaustive classification ensures that no two different `r`
values in (6.1) represent a hidden larger frequency class.

For every `m>=0`, set

```text
t=2*m,
q=2^(m+1).
```

The machine-checked `N_evenScale` and `H_evenScale` give

```text
N_(2m)=q^2+1,
H_(2m)=q+1.                                              (6.2)
```

Substituting (6.2) into (6.1), then using `j=r-1`, gives

```text
M_(2m)
  = 2*sum_(j=0)^(q-1) (q-j)*(q^2-(j+1)).                (6.3)
```

T81 defines the right side as `originalPairedMass q`.
`pairedMass_eq_original` proves its equality with a reflected,
subtraction-free sum, and `pairedMass_evenScale_literal` ties it directly to
the literal `H_(2m),N_(2m)` expression in (6.1).

## 7. Exact mass and strict normalized excess

The machine-checked `pairedMass_formula` evaluates (6.3):

```text
M_(2m) = q*(q+1)*(q-1)*(3*q+2)/3.                       (7.1)
```

Since the T69 coefficient target is `H*N`, (6.2)--(7.1) give

```text
M_(2m)/(H_(2m)*N_(2m))
  = q*(q-1)*(3*q+2)/(3*(q^2+1))
  >= (4/5)*(q-1).                                       (7.2)
```

Theorems `pairedMass_normalized` and `pairedMass_normalized_lower` check both
claims in (7.2). The constant `4/5` follows after clearing the positive
denominator from

```text
(q-1)*(3*q^2+10*q-12) >= 0,
```

which holds for `q>=2`.

Because `q=2^(m+1)` is unbounded, (7.2) is a strict quantitative obstruction:
for every real `C`, some `m` satisfies

```text
C*H_(2m)*N_(2m) < M_(2m).                               (7.3)
```

`exists_evenScale_mass_exceeds` machine-checks (7.3), including the
quantifier over every real `C`. This is the requested third exit: the complete
interior equal-frequency family has normalized coefficient mass tending to
infinity, and the proposed adjacent-index involution adds every pair instead
of cancelling it.

## 8. Exact conclusion and limitations

T81 refutes only the mechanism "pair the `h=10,k` term with the equal-frequency
`h=1,k+1` term to obtain cancellation." Those terms have the same phase and
same positive coefficient, and their normalized paired coefficient mass is
unbounded along the explicit infinite even-scale family.

Coefficient mass is not a lower bound for the value of a trigonometric sum.
Unequal frequencies in (4.5)--(4.6) may still cancel at `alpha=pi`. Therefore
T81 proves no fixed-`pi` aggregate estimate, no strict saving for the complete
signed sum, no T69 primitive budget, no T29 predicate, and no conclusion for
C1, C2, C3, or the canonical collision question. Those remain open.

## 9. Machine-checked theorem map

All declarations are in the fresh namespace
`Theory.PiDigits.LongLagBlockCollisionDecay.T81`.

| Requirement | Lean declarations |
|---|---|
| Pair domain and involution | `InteriorPairDomain`, `adjacentSwap`, `adjacentSwap_mem`, `adjacentSwap_involutive`, `adjacentSwap_ne` |
| Exhaustive T76 classes | `equalFrequencyClass_exact` |
| Equal frequency and same sign | `adjacentFrequency_eq`, `pooledTerm`, `adjacentTerms_equal`, `adjacentTerms_add`, `adjacentCoefficient_pos` |
| Boundary fibers | `leftBoundary_frequencyClass`, `rightBoundary_frequencyClass` |
| Unequal cutoff | `unequalCutoff_iff` |
| Original coefficient family | `originalPairedMass`, `pairedMass_eq_original`, `pairedMass_evenScale_literal` |
| Exact even scales | `evenScaleBase`, `N_evenScale`, `H_evenScale` |
| Exact normalized mass | `pairedMass_formula`, `pairedMass_normalized`, `pairedMass_normalized_lower`, `evenScale_normalized_lower` |
| Strict quantitative exit | `evenScale_mass_exceeds`, `exists_evenScale_mass_exceeds` |

## 10. Skeptic checklist

1. Hash `CANONICAL_STATEMENT.txt` and compare it with Section 1.
2. Compare (2.1)--(2.3) with T69's `aggregateEnergy_literal`.
3. Compare (3.1) with T76's `pooledFrequency_eq_iff` and finite literal form.
4. Check that (4.2) preserves (4.1), is fixed-point-free, and has both stated boundaries.
5. Check the plus signs and factor `2*w_r` in (4.3).
6. Check that (4.5)--(4.6) retain all ten frequencies and each `L_r=N-r`.
7. Check the exact common cutoff `N-max(r,r')` in (5.1)--(5.2).
8. Check the pair count `N-r-1` and the literal mass (6.1).
9. Check the even-scale identities, exact formula (7.1), and normalization (7.2).
10. Check the all-`C` strict inequality (7.3) and the limited conclusion in Section 8.
