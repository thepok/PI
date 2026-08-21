# T105: bounded energy, flattening, and sum-product scout for `D_N`

Search date: 2026-08-10 UTC.

Claim labels: `literature-checked` for the five source statements pinned in
`SOURCE_PINS.md`; `proof sketch` for the elementary substitutions and negative
map in this report; `experiment` for the bounded exact-arithmetic replay in
`verify_t105.py`. No Lean theorem is added.

`PRIMARY_SOURCE_COUNT: 5` (cap: 8)

`CANDIDATE_COUNT: 3` (cap: 3)

`TERMINAL_DECISION_COUNT: 1`

This note proves no estimate for fixed pi, no canonical A1/C1 statement, no C2,
no normality statement, and no decimal-factor-complexity statement.

## 1. Immutable statement and scope

The byte-exact `canonical_statement.txt` has SHA-256

```text
cbf56699b651aeb69301265763e38da44feb59c6fd955d2280887e8c06c6a2f8
```

For integers `n,N>=1`, the canonical question defines

```text
Q_pi(n,N) = #{(i,j) in {0,...,N-1}^2:
               ||(10^i-10^j)pi||_(R/Z) < 10^(-n)}.
```

Pairs are ordered, the diagonal is included, and the inequality is strict. The
open quantifiers are

```text
for every A>=1, for every sufficiently large n,
there exists N=N(A,n)>=1 with A*n*Q_pi(n,N)<=N^2.
```

The present item studies the A13/A14 mechanism set

```text
D_N = {10^i-10^j : 0<=i,j<N}
```

over the integers and after reduction modulo a prime. Metric, rational, finite,
or other-point results are sibling information only. T10 is a sufficient
Fourier strategy and a necessary obstruction under failure, not a replacement
for the canonical statement.

The notation `D_N` below always means this set. It does not mean discrepancy or
the unrelated grouped-square quantity bearing the same letter in older notes.

## 2. Exact elementary structure of `D_N`

Put `X_N={10^j:0<=j<N}`. If `i>j`, then

```text
10^i-10^j = 2^j 5^j (10^(i-j)-1),
```

and the last factor is divisible by neither 2 nor 5. Thus either valuation
recovers `j`, after which the magnitude recovers `i`. Sign distinguishes
`i>j` from `i<j`. Therefore all nonzero ordered differences are distinct and

```text
|D_N| = N(N-1)+1.                                           (2.1)
```

This proof is over the integers. Reduction modulo a prime `p` is injective on
`D_N` under the explicit sufficient condition

```text
p > 2(10^(N-1)-1).                                         (2.2)
```

Without (2.2), source theorems must use the actual deduplicated residue set.

There is also an exact large-doubling witness. For every
`0<=a<b<c<d<N`,

```text
(10^b-10^a)/9 + (10^d-10^c)/9
```

has base-10 digits exactly one on the two disjoint intervals `[a,b)` and
`[c,d)`, and zero elsewhere. The four endpoints are therefore recoverable.
These `binom(N,4)` values are distinct elements of `(D_N+D_N)/9`, so

```text
|D_N+D_N| >= binom(N,4),
|D_N+D_N|/|D_N| >= binom(N,4)/(N(N-1)+1).                  (2.3)
```

In particular, the full integer set has doubling at least order `N^2`; it is
not a bounded-doubling family.

Finally, for `e(x)=exp(2*pi*i*x)` and every real `t`, uniqueness of the nonzero
differences gives

```text
sum_(d in D_N) e(td)
  = |sum_(j=0)^(N-1) e(t10^j)|^2 - N + 1.                 (2.4)
```

The ordered square has `N` copies of zero, whereas the set sum has one. Thus
additive-set Fourier decay on `D_N` is not itself the linear cancellation T10
needs: (2.4) makes it a squared version of exactly that missing orbit sum.

`verify_t105.py` enumerates `D_N` for `1<=N<=12`. It checks (2.1), the explicit
witnesses in (2.3), additive energy, product-set cardinality, and the displayed
finite polynomial patterns. These are `experiment` results only. They may
reject a proposed bounded-doubling or high-energy model at those parameters;
they do not prove a universal formula or any statement about pi.

## 3. The exact T10 transfer budget

The machine-checked T10 interface says that literal failure of canonical A1
would provide fixed `A>=1`, arbitrarily large `n`, and, for every requested
`K>=1`, integers

```text
N=16*A*n*K,  1<=r<N,  J=N-r>=K,  1<=h<=256*A*n             (3.1)
```

with

```text
|sum_(j=0)^(J-1) e(h(10^r-1)10^j*pi)|
  > J/(131072*A^2*n^2).                                   (3.2)
```

Locator: `T10LongLagResonance.lean`, theorem
`not_canonical_C1_implies_arbitrarily_long_lag_resonance`, lines 829-894.
The coefficient `h(10^r-1)10^j` is `h(10^(r+j)-10^j)`, one fixed-lag slice of
`hD_N`, not the complete difference set.

For later rational comparisons, let `theta=a/p`. Since
`|e(x)-e(y)|<=2*pi*|x-y|`, summing the geometric coefficients gives

```text
|S_J(pi)-S_J(theta)|
 <= (2*pi/9)|pi-theta| h(10^r-1)(10^J-1).                 (3.3)
```

Spending half of the threshold in (3.2) is justified by the explicit premise

```text
|pi-a/p| <=
  9J/[524288*pi*A^2*n^2*h(10^r-1)(10^J-1)],               (3.4)
```

and leaves the modular cancellation target

```text
|sum_(j=0)^(J-1) e_p(a*h(10^r-1)10^j)|
 <= J/(262144*A^2*n^2).                                   (3.5)
```

Equations (3.3)-(3.5) are elementary conditional bookkeeping, not an asserted
approximation theorem for pi.

## 4. Candidate 1: energy decomposition and inverse energy

### Source theorem and range

Rudnev-Shkredov-Stevens (S1), Theorem 5, says that for finite `B` in a field
with the paper's standing conventions

```text
0 notin B,  |B|>1,                                           (4.0)
```

there is `B' subset B`, `|B'|>=|B|/2`, with

```text
min(E_plus(B'), E_times(B'))
  <= C |B|^(3-delta)(log |B|)^c,                            (4.1)
```

where `delta=1/4` over the complex numbers and `delta=1/5` over an arbitrary
field, with `|B|<=p^(5/8)` in characteristic `p`. Here (4.1) expands the
source's comparison notation: some absolute `C,c>0` are suppressed, and the
source does not calculate the logarithmic power `c`.

Bloom (S2), Theorem 8, states for every `epsilon>0` that if a finite set in an
abelian group obeys

```text
E_plus(B) >= K^(-1)|B|^3,                                  (4.2)
```

then some `B' subset B` has

```text
|B'| >>_epsilon K^(-100/81-epsilon)|B|,
|B'-B'| <<_epsilon K^(100/27+epsilon)|B'|.                 (4.3)
```

S2 is a 2025 preprint. It is used as a source-pinned candidate theorem, not
represented as independently refereed or machine-checked here.

### Literal substitution and cheap discriminator

For prime `p` set

```text
B = (D_N mod p) without {0},  m=|B|.                       (4.4)
```

Always `m<=N(N-1)`. Hence in the regime `N<=C log p`, the S1 size hypothesis

```text
m^8 <= p^5                                                  (4.5)
```

holds for all sufficiently large `p`, for each fixed `C`. If (2.2) also holds,
then `m=N(N-1)` exactly, so (4.0) holds for `N>=2`. Without (2.2), the exact
additional cardinality discriminator is `m>1`; deleting zero already gives
`0 notin B`. Thus S1 genuinely applies in a logarithmic regime whenever these
explicit tests pass, but
its output is only an unlocated half-sized subset and an either/or conclusion:
it neither bounds the energy of all `D_N` nor says which energy is small.

The exact integer full-set doubling test (2.3) grows like `N^2`. It transfers
to (4.4) when (2.2) makes reduction injective. Without (2.2), modular
collisions can alter both cardinality and doubling, so the exact cheap residue
test is to compute `|B+B|/m` rather than import (2.3). In either case, the
cheapest exact inverse-energy test is

```text
K_D = m^3/E_plus(B).                                       (4.6)
```

S2 is informative only to the extent that this computed `K_D` is small enough
for (4.3) to retain a useful subset. The replay computes the integer model
through `N=12`; the observed energy is order `m^2`, not near-maximal `m^3`.
This selects (4.6) as the cheapest future test but is not a proof of its
asymptotics modulo primes.

### Required pi-specific premise

To transfer this candidate toward T10 one would need, uniformly for every
adaptive tuple (3.1), a prime `p`, numerator `a`, and a subset/flattening
argument that does all of the following:

```text
(E1) satisfies the approximation budget (3.4);
(E2) retains the exact fixed-lag progression {10^j:0<=j<J}, not merely an
     unspecified half-subset of D_N;
(E3) converts the energy alternative into the pointwise character bound (3.5)
     at lambda=a*h(10^r-1) mod p.                           (4.7)
```

Neither S1 nor S2 supplies (E1), locates the adaptive character in (E3), or
turns small energy into a pointwise Fourier estimate. Assuming (E3) without an
independent flattening theorem simply renames the T10 cancellation target.

**Disposition:** applicable structural model, but no transfer survivor.

## 5. Candidate 2: Fourier-decaying lacunary dynamics

### Source theorem and range

Tan-Zhou (S3), Theorem 1.7, assumes a probability measure `mu` on `R^d` with
polylogarithmic Fourier decay. Its proof makes the exact exponent range explicit:

```text
|mu_hat(t)| << (log |t|)^(-alpha) for some alpha>0,          (5.1)
```

a sequence of expanding integral matrices `A_j`, and

```text
sigma_min(A_(j+1) A_j^(-1)) >= K>1.                        (5.2)
```

It concludes that `(A_j x)` is equidistributed modulo one for `mu`-almost every
`x`. The stronger condition `s>d+1` printed in Theorems 1.8 and 1.10 belongs to
the paper's quantitative shrinking-target result, not the exact range of
Theorem 1.7 used here. This is a metric theorem, not a theorem for every point
in the support.

### Literal substitution and cheap discriminator

Take `d=1`, `A_j=[10^j]`, and `K=10`. Then (5.2) is exact. For each fixed
nonzero integer `k`, Weyl's criterion gives, for `mu`-almost every `x`,

```text
sum_(j<N) e(k10^j x) = o(N).                               (5.3)
```

Substitution into (2.4) gives an `o(N^2)` complete-set Fourier coefficient for
`D_N`. There is no energy, doubling, modulus, or minimum-size hypothesis on
`D_N`: the exact discriminator is instead whether the point lies in the
source theorem's full-measure set for a measure satisfying (5.1).

For `x=pi`, no such membership statement is supplied. Taking `mu=delta_pi`
does not pass (5.1), since every Fourier coefficient of a point mass has
absolute value one.

### Required pi-specific premise

T10 needs more than qualitative cancellation for each fixed `k`. The required
additional premise is a quantitative, pi-specific uniform version:

```text
(F1) for all sufficiently large canonical n, every legal adaptive
     r,h,J in (3.1) satisfies
     |sum_(j<J)e(h(10^r-1)10^j*pi)|
       <= J/(131072*A^2*n^2).                              (5.4)
```

Alternatively one could give a Fourier-decaying `mu`, prove pi belongs to a
quantitative exceptional-set complement uniform over the same adaptive box,
and derive (5.4). S3 supplies neither membership nor this rate. The premise
(5.4) is the T10 sufficient estimate itself, so the metric theorem has not
reduced the fixed-point problem.

### Prior-fingerprint classification

The staged T104 report, SHA-256
`2dee0c91ce8480785a851df4aad06e0ab65f92e647fa7f67605b868129fc16d5`,
labels its new deductions as a `proof sketch`. Its F4 card (Section 6.4,
report lines 443-527) starts from Baker--Banaji Theorem 1.2, Proposition 2.5,
and Theorem 2.7, derives an ambient-measure `L^2` estimate for the same
geometric phase sum, and stops because `delta_pi` has Fourier coefficients of
modulus one while ambient almost-everywhere control neither locates pi nor
gives adaptive-multiplier uniformity. Candidate 2 has the same normalized
fingerprint and the same first fatal gap. It is therefore a **T104-F4
duplicate**, not a new survivor. Tan--Zhou supplies a different source theorem
and weaker polylogarithmic measure decay, but that does not change the
mechanism classification.

**Disposition:** duplicate model-only comparator; pointwise membership and
quantitative uniformity fail before any `D_N` energy test becomes relevant.

## 6. Candidate 3: modular geometric-progression sums

### Incomplete sums

Kerr (S4), Theorem 2, fixes a prime `p`, an element `g` of order `t`, and
`N<=t`. For

```text
S_(g,p)(lambda,N)=sum_(j=1)^N e_p(lambda*g^j),
```

its first range `N<=t^(1/2)` gives

```text
max_(lambda!=0)|S_(g,p)(lambda,N)|
 <= p^(1/8) N^(71/96+o(1)).                               (6.1)
```

The source gives two further ranges in Theorem 2 and complete-order bounds in
Theorem 3. Substitute `g=10 mod p`, `t=ord_p(10)`, and
`lambda_target=a*h(10^r-1) mod p`. Kerr indexes its source sum from `j=1`
through `J`, while (3.5) starts at zero. The exact source character is therefore

```text
lambda_source = lambda_target*10^(-1) mod p.                (6.2a)
```

The inverse exists because `p` does not divide 10. The exact basic order test
for Theorem 2 is

```text
p does not divide 10, lambda is nonzero, J<=ord_p(10).      (6.2)
```

The displayed first-range bound (6.1) has the further indispensable branch
condition

```text
J <= ord_p(10)^(1/2).                                      (6.2b)
```

Thus the exact applicability test for (6.1) is (6.2) plus (6.2b), not merely
the order bound. Even granting both, the main powers in (6.1) beat the trivial
length `J` only past

```text
J > p^(12/25+o(1)),                                       (6.3)
```

because `p^(1/8)J^(71/96)<J` is equivalent at the displayed powers to
`J>p^(12/25)`. In the agenda regime `N asymp log p`, T10 gives only
`J<=N=O(log p)`; that upper bound already places `J` outside the nontrivial
range by a polynomial factor. No lower comparison between `J` and `log p` is
used. The other displayed Kerr ranges do not repair logarithmic length.

### Complete subgroup sums

Di Benedetto et al. (S5), Theorem 3.1, assumes a complete subgroup
`H subset F_p^*` of order

```text
p^(1/4)<H<p^(1/2)                                          (6.4)
```

and proves

```text
max_(a!=0)|sum_(x in H)e_p(ax)|
 <<subpower H^(2689/2880)p^(1/72).                         (6.5)
```

For `H=<10>`, the prefix `{10^j:0<=j<J}` is the full subgroup exactly when
`J=ord_p(10)` and each element is used once. Combining this with (6.4) requires
`J>p^(1/4)`, which is incompatible with `J<=N=O(log p)` for large `p`. This is
the exact completeness/scale discriminator; no finite computation is needed.

### Required pi-specific premise

A modular route must provide, uniformly for every adaptive T10 tuple,

```text
(M1) a prime p and numerator a satisfying (3.4);
(M2) nonzero lambda_target, the shifted character (6.2a), the order range
     (6.2), and the first-branch condition (6.2b) when invoking (6.1);
(M3) a logarithmic-length theorem proving the pointwise bound (3.5). (6.6)
```

S4 does not reach (M3) at `J=O(log p)`; S5 applies only to the complete
polynomial-sized orbit. Approximation alone does not supply modular
cancellation, and modular cancellation without (3.4) does not transfer to pi.

**Disposition:** source hypotheses fail at the required scale.

## 7. Comparison with prior fingerprints

Verification levels are part of this comparison. A `proof sketch` note is
navigation and warning only, not a discharged premise.

| prior item | status used here | normalized fingerprint | comparison with T105 |
|---|---|---|---|
| T10 | machine-checked Lean interface | failure gives one adaptive fixed-lag low-harmonic resonance with constants (3.1)-(3.2) | T105 preserves its fixed-lag slice and exact threshold; none of the three candidates bounds that slice |
| T45 | source statements literature-checked; mixed-support transfer is a proof sketch | large sieve, fixed-multiplier lacunary bounds, uniform Sidon, and dissociation do not control the mixed prescribed coefficient | Candidate 1 adds an energy/BSG fingerprint, but its unlocated subset and either/or conclusion still do not evaluate the prescribed character |
| T73 | machine-checked Lean interface | one parent resonance yields many child resonances with product-difference coefficients, without compatibility | Energy information on `D_N` does not create compatibility among T73 children |
| T81 | proof sketch using checked T73/T28 types and one pinned source | scalar irrationality packing is vacuous at exponential coefficient height | Candidate 3 uses modular cancellation rather than scalar packing, but fails earlier at logarithmic length |
| T87 | mixed literature-checked sources, checked quoted types, and proof-sketch substitutions | negative synthesis leaves adaptive fixed-pi cancellation open; numerator-conductor bounds exceed the logarithmic budget | Equations (3.4)-(3.5) retain its exact rational-transfer boundary; no conductor claim is imported as proved |
| T90 | literature-checked source statements; fixed-point transfer is a proof sketch | named dynamical models have discrepancy, but pi lacks point membership | Candidate 2 is the same metric-membership obstruction with a newer Fourier-decay theorem, not a fixed-point advance |
| T91 | literature-checked sources; collision formulas are proof sketches | automatic models synchronize aligned or canonical samples but lose full-prefix mass or multiplicity | Its symbolic collision energy is not additive energy of `D_N` |
| T92 | machine-checked constant-run discriminator | exact-word short collisions charge to long collisions with a family constant | No circle character or `D_N` additive-energy estimate follows |
| T93 | proof sketch with pinned source statements | Stoneham rational skeleton gives repeated modular residues | Exact modular repetition is occupancy, not cancellation at the T10 adaptive numerator |
| T94 | proof sketch and experiment | finite paperfolding carry recurrence for symbolic collisions | Finite-state symbolic energy is distinct from convolution flattening of `D_N` |
| T95 | proof sketch | universal period charging for exact words | Similar energy language, different object; no additive quadruple or Fourier conclusion for `D_N` |
| T96 | proof sketch with literature-checked source statements | prime-family Stoneham skeleton and non-Poissonian sibling | Difference factors rewrite phases but do not make them cancel |
| T97 | proof sketch and experiment | exact paperfolding diagonal collision asymptotics | Model collision asymptotics do not evaluate a fixed pi coefficient |
| T98 | proof sketch using checked imports | exact-word charging transports only conditionally through collision comparison; Vaaler reversal is invalid | Candidate 1 likewise cannot reverse an energy statement into a pointwise Fourier upper bound |
| T99 | proof sketch with literature-checked source statements | exceptional-prime repeated modular skeleton | Divisibility of elements of `D_N` is not small energy or adaptive Fourier decay |
| T100 | machine-checked Lean theorem | formal universal finite-word period charging | Checked exact-word energy remains a different statistic from `E_plus(D_N)` |
| T101 | proof sketch and experiment | paperfolding collision energy has only `O(1/n)` relative one-step loss | This is symbolic non-flattening, not convolution flattening over a field |
| T102 | proof sketch with literature-checked source statements | general coprime Stoneham order profiles and stable coset multiplicity | Complete rational orbit structure repeats Candidate 3's scale/completeness failure |
| T103 | source statements `literature-checked`; collision translations and deductions are a `proof sketch`; report SHA `ed690a31fbc19d08c817bcb2558ec259788e37d4f8243261ece1b9eafbbb5df0` | explicit positive-entropy Toeplitz point with nested power-of-five periodic-hole towers, exact hole density `delta_R>3/4`, and collision lower bounds but no upper collision or successor-splitting estimate | Distinct from all three T105 candidates: symbolic periodic-hole repetition is neither additive energy of `D_N`, ambient Fourier decay, nor modular geometric-sum cancellation; it supplies no transfer premise used here |
| T104 | twelve source statements `literature-checked`; fingerprint deductions are a `proof sketch`; report SHA `2dee0c91ce8480785a851df4aad06e0ab65f92e647fa7f67605b868129fc16d5` | F4: nonlinear self-conformal measure Fourier decay gives ambient `L^2` control of the exact geometric sum, but `delta_pi` fails decay and no named-point adaptive maximal theorem is supplied | Candidate 2 duplicates F4's ambient Fourier-decay mechanism, named-point failure, and adaptive-uniformity premise; Candidate 1's energy/BSG subset alternative and Candidate 3's logarithmic modular-sum scale obstruction remain distinct |

The supplied semantic obstruction memory is an unverified audit ledger. Its
relevant warnings are respected rather than used as premises: collision
classification and frequency injectivity do not evaluate the prescribed pi
coefficient; exact phase regrouping is not cancellation; model behavior is not
fixed-point evidence; and many resonant children do not imply compatible
cross-row cancellation. T105's three failures instantiate these warnings with
new source-pinned theorem tests rather than assuming them. The now-staged T103
comparison adds no overlapping `D_N` mechanism. The T104 comparison removes
Candidate 2 from the novelty count: its separate source pin does not make the
ambient-measure fingerprint new.

## 8. Negative map and replay

| candidate | exact cheap test on `D_N` or its orbit | result in `N asymp log q` | first missing pi-specific premise |
|---|---|---|---|
| energy/BSG | `(2.1)`, integer `(2.3)`, injectivity `(2.2)` or direct modular `|B+B|/m`, `m^8<=p^5`, and `K_D=m^3/E_plus(B)` | S1 size condition passes; integer or injective-reduction bounded doubling fails, while a colliding residue set requires direct testing; the source still returns only an either/or subset | `(E1)-(E3)`, especially pointwise flattening at the adaptive T10 character |
| Fourier-decay dynamics | `A_j=10^j`, ratio singular value exactly 10, measure decay `(5.1)` | matrix hypothesis passes; fixed-point membership and quantitative rate are absent; this repeats T104-F4's ambient-measure/named-point obstruction | `(F1)` or an independently proved quantitative genericity theorem containing pi |
| modular orbit sums | order tests `(6.2)` and `(6.2b)`, Kerr threshold `(6.3)`, complete-subgroup condition `(6.4)` | all available nontrivial estimates require polynomial, not logarithmic, length | `(M1)-(M3)`, especially a new logarithmic-length pointwise sum theorem |

Replay from a directory containing only the delivered files:

```text
python3 verify_t105.py
sha256sum -c SHA256SUMS
```

The script checks every delivered source hash and theorem anchor; parses this
report for all named comparator rows, the three candidate cards, the displayed
T10/transfer constants, the caps, and one terminal choice; checks the canonical
hash and two load-bearing quantifier phrases; and replays exact finite `D_N`
cardinality, energy, doubling witnesses, product counts, and four modular scale
comparisons. The local prior-art pins in `SOURCE_PINS.md` identify the supplied
library files used for the comparison; they are not copied into this capped
package. Finite output is selection/rejection evidence only.

TERMINAL VERDICT (1/1): **CLOSE WITH A SOURCE-PINNED NEGATIVE MAP.** Candidate 2 contributes no new survivor because it duplicates T104-F4. Independently of that duplicate, Candidate 1 does not turn its energy/subset alternative into the prescribed character bound, and Candidate 3's incomplete and complete modular theorems require polynomial-length or complete orbits rather than the logarithmic T10 range. T103 is a distinct symbolic periodic-hole model and supplies no `D_N` transfer. Thus Candidates 1 and 3 still justify the terminal negative map. Do not schedule another generic additive-energy, flattening, sum-product, or geometric-sum scout for this fingerprint. Reopen only for a theorem that directly supplies one of `(E1)-(E3)` or `(M1)-(M3)` at the exact T10 constants, or genuinely discharges the already-recorded T104-F4 pointwise premise rather than renaming `(F1)`. This closes only the audited mechanism fingerprint and makes no fixed-pi, C1, or C2 claim.
