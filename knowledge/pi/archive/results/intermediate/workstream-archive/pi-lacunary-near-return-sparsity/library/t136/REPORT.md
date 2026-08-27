# T136: post-T133 cross-domain delta scout

Status: `literature-checked` source audit dated 2026-08-10, with T134/T135
status reconciliation refreshed 2026-08-12; all transfer
comparisons below are `proof sketch` deductions unless a machine-checked prior
interface is explicitly named.

SOURCE_COUNT: 6
DOMAIN_COUNT: 3
SURVIVOR_FINGERPRINT_COUNT: 0
NEGATIVE_CARD_COUNT: 3
SUCCESSOR_COUNT: 0
OVERALL_VERDICT_COUNT: 1

## 1. Provenance and normalized statement

The immutable source is `canonical_statement.txt`, a byte-exact copy of
`knowledge/pi/statements/pi-lacunary-near-return-sparsity.txt`, with SHA-256

```text
cbf56699b651aeb69301265763e38da44feb59c6fd955d2280887e8c06c6a2f8.
```

For integers `n,N>=1`, it defines

```text
Q_pi(n,N)=#{(i,j) in {0,...,N-1}^2:
             ||(10^i-10^j)pi||_(R/Z)<10^(-n)}.
```

Pairs are ordered, all `N` diagonal pairs are included, and the cutoff is
strict. Canonical A1 asks

```text
for every A>=1 there exists n0>=1 such that for every n>=n0
there exists N=N(A,n)>=1 with A*n*Q_pi(n,N)<=N^2.
```

This is not collision-C1. The immutable statement's A10 calls its parent-program
exact-factor collision-energy hypothesis C1, records it as weaker, and
attributes only the implication from A1 to T8. Separately, T7 has a legacy
theorem name containing `canonical_C1`, but that theorem's literal left-hand
side is canonical A1 and its right-hand side is T7's finite cylinder-energy
frontier. T136 follows theorem types and the immutable A10 label, not the legacy
name; it does not assert the converse for collision-C1/A10.

### Ambiguities fixed before the scout

1. A source is primary only if its paper PDF was opened; prior reports are
   comparators and are not counted in `SOURCE_COUNT`.
2. A theorem about an ambient measure is not a theorem about the prescribed
   point `pi`; support membership would still not imply typicality.
3. A complete cyclic subgroup and an ordered initial segment are different
   objects, even if both can be written with powers of 10.
4. A bound larger than the trivial length bound is quantitatively
   noninformative. It does not show that the actual sum is large.
5. Failure of a source hypothesis is theorem inapplicability. A counterexample
   to a broader proposed transfer principle is called falsification only for
   that principle.
6. T130--T133 source statements are used at `literature-checked` level and
   their new deductions at `proof sketch` level. No prose deduction is treated
   as a machine-checked premise.
7. T134 and T135 are now readable accepted literature artifacts, but remain
   exclusions rather than evidence for T136. Their source statements are used
   only at their self-labeled `literature-checked` level; their deductions
   remain `proof sketch` and are not discharged premises here.

## 2. Target interfaces and quantitative screens

The following accepted Lean interfaces are targets, not supplied estimates.

### T7

The T7 machine-checked interface records the ordered, diagonal-inclusive
decimal-cylinder energy `E_pi(n,N)` and

```text
E_pi(n,N) <= Q_pi(n,N) <= 3*E_pi(n,N).
```

A direct collision-energy route to canonical A1 therefore needs, after
replacing `A` by `3A`, some prefix satisfying

```text
E_pi(n,N) <= N^2/(3*A*n).                       (T7-screen)
```

### T10

The T10 machine-checked obstruction is conditional on failure of canonical A1.
Despite legacy declaration names containing `canonical_C1`, its theorem type
literally negates the `Q_pi` quantifier above. It forces adaptive sums with
`1<=h<=256*A*n`, lag `r`, length `M=N-r`, and

```text
M/(131072*A^2*n^2)
  < |sum_(0<=j<M) exp(2*pi*i*h*(10^r-1)*10^j*pi)|.       (T10-screen)
```

A useful cancellation theorem must address the prescribed point, adaptive
coefficient `h(10^r-1)`, and arbitrarily long initial segments.

### T28

T28's machine-checked bridge requires compatible witnesses at two adjacent
nodes of one resonance chain, the exact cross-error condition

```text
Q0*e1 + U*Q1*e0 < 1,
```

and explicit denominator/error bounds strong enough to meet an exponent-eight
irrationality lower bound. A theorem about separate frequencies or an averaged
parameter law supplies no such adjacent-node compatibility.

### T107

At every retained level `ell` and prefix `P`, T107's machine-checked
conditional interface keeps two separate budgets:

```text
rowBoundaryLoad(ell,P) <= P/(40*10^ell),
|rowFourierRemainder(ell,P)| <= P^2/(10*10^ell).          (T107-screen)
```

These must hold on a positive-density triangular family along one increasing
pi-prefix sequence. Fixed-frequency convergence or a limiting one-symbol law
does not meet this screen.

## 3. T129 correction and post-T129 delta

`PRIOR_EVIDENCE.tar` vendors the exact evidence used in this section.

### Corrected T129 label

The T129 review record identifies one defect in its exclusion table: T106 was
labeled "Failure of C1." The vendored T106 theorem
`literal_not_canonical_C1_implies_finite_branching_resonanceTree` has a legacy
name and comment, but lines 300--302 literally assume

```text
not (for every A>=1 there exists n0>=1 such that for every n>=n0
     there exists N>=1 with A*n*Q_pi(n,N)<=N^2).
```

**Corrected label:** `Failure of canonical A1 (legacy declaration name mentions
C1)`. It is not failure of collision-C1/A10. No C1 conclusion is imported from
T129.

### Exact T130--T133 disposition cards

| Item and level | Exact post-T129 delta | Disposition carried into T136 |
|---|---|---|
| T130: source claims `literature-checked`, deductions `proof sketch`, replay `experiment` | Literal equal positive decimal blocks become S-unit/group equations, but available common rank is `N+O(log N)`. The sourced counts exceed the required `N` or `N^2` ceilings; the zero block is degenerate and separately needs `c_0=o(N/sqrt(m))`. The report's conditional rank threshold is `rho*kappa<0.415241...` for its first card. | Close direct standard S-unit/Subspace-theorem counting. Preserve growing-rank and zero-fiber occupancy as separate obstructions. |
| T131: source claims `literature-checked`, deductions `proof sketch`, replay `experiment` | Balanced fractional de Bruijn flow rounds to integral circulation and a complete Euler tour, but partial-prefix constants are unscaled. Coherent multiscale realizations reduce to the already represented global-L2 or offline incidence constructions. | Close cycle-flow rounding/ordering as a new route. Prefix control, not integrality, is the first unresolved interface. |
| T132: source claims `literature-checked`, deductions `proof sketch`, replay `experiment` | The finite majorization meet can strictly improve every single projection bound: the checked example is `C=22 < G=38 < min=44 < average=47`. No theorem supplies the required joint profiles for pi. | Hold only the strict finite projection-majorization model; do not tensorize marginal Renyi-2 information. |
| T133: source claims `literature-checked`, deductions `proof sketch`, replay `experiment` | A complete three-state, 15-transition base-5 valuation transducer gives exact extrema for the H1 coefficient model, but reduced rational orbit length remains `N asymp log q`. The proposed continuation is substantively the earlier unproved `PI-H1-COLL` injection under a new name. | Close valuation refinement of H1; reject renamed arithmetic continuation and retain the logarithmic-length obstruction. |

These are disposition cards, not theorem promotions. T136 does not rederive their
broad inventories.

## 4. T134/T135 reservation reconciliation

The original binding orchestration snapshot, vendored in `PRIOR_EVIDENCE.tar`,
records generation-1 startup leases for T134 and T135. That historical state is
now superseded for comparison purposes: the refreshed knowledge snapshot
contains both accepted reports, vendored byte-exactly as `t134/REPORT.md` and
`t135/REPORT.md`. Acceptance is not proof. Each report labels its pinned source
statements `literature-checked`, its new deductions `proof sketch`, and its
finite replay `experiment`; T136 preserves those levels.

| Item | Reserved lane | Current readable disposition | T136 action |
|---|---|---|---|
| T134 | zero-fiber occupancy | The report's sole scoped verdict is `close`: its restricted-approximation and G-value bounds fail the displayed one-fiber occupancy screen, while its constructed de Bruijn model duplicates prior global incidence. It separately labels `PI-ZERO-OCCUPANCY` a `conjecture`; even that premise leaves every positive cylinder uncontrolled. | Continue excluding zero-block/zero-fiber occupancy as a T136 novelty lane. Do not infer the conjectural premise or any total-energy estimate. |
| T135 | Renyi-2 tensorization | The report's sole scoped verdict is `HOLD AS MODEL`: it rejects unconditional coordinate-projection tensorization and retains only a separated independent-convolution model. Its `PI-PROJECTION-TRANSFER-T135` shrinking-scale empirical-law premise is explicitly conjectural and rejected there as carrying essentially the target burden. | Continue excluding marginal Renyi-2 tensorization. Do not count the held independent-convolution model as a T136 source or survivor and do not infer its fixed-pi transfer premise. |

These status changes resolve availability only. They add no source to T136's
six-source ledger, no survivor fingerprint, and no mathematical evidence for
the prescribed decimal orbit. The T134 one-fiber premise and T135 empirical-law
premise are both outside the present scout and remain unproved.

## 5. Complete six-source delta ledger

Every PDF is new to the supplied semantic memory through T133 by exact-title,
author, arXiv-ID, and file-name search on 2026-08-10. URLs, DOI links, hashes,
theorem hypotheses, and locators are in `SOURCE_PINS.md`.

| ID | Domain | Primary source | Exact inspected result | Initial decision |
|---|---|---|---|---|
| M1 | Mahler/functional equation | Coons--Evans--Manibo (2022) | Definition 1, Theorem 1, Corollary 2, Theorem 5 | Screen exact matrix Mahler/Fourier cocycle; fail at absent 10-regular representation and finite-prefix rate. |
| M2 | Mahler/functional equation | Cassaigne--Espinoza--Rigo--Stipulanti (2026) | Theorem 18, Lemma 19, Proposition 20, Lemmas 23--25 and `||zeta_2||_infty<=20/27` | Screen exact adic desubstitution contraction; fail at absent decimal recurrence and finite-`N` pair bound. |
| F1 | arithmetic/fractal Fourier decay | Baker--Banaji (2026) | Theorems 1.3 and 1.7 | Retain only as falsification of a broad qualitative Rajchman transfer principle, not as a fixed-pi mechanism. |
| F2 | arithmetic/fractal Fourier decay | Baker--Khalil--Sahlsten (2024) | Definition 1.1 and principal Theorem 1.5 | Screen Diophantine separation and polylogarithmic decay; natural decimal ratios and the point mass both fail exact hypotheses. |
| X1 | short structured exponential sums | Ostafe--Shparlinski--Voloch (2022/2023) | Theorem 2.4 and Remark 2.6 | Direct scalar `10^j` specialization is legal, but completion is quantitatively trivial at logarithmic length. |
| X2 | short structured exponential sums | Ostafe--Shparlinski--Voloch (2023/2024) | Theorem 1.1 | Complete-subgroup power saving starts at `tau>=p^(3/7+epsilon)` and gives no logarithmic prefix estimate. |

No paper is counted twice. The ledger stops at six, below the cap of twelve.

## 6. Domain negative cards

There are no retained survivor fingerprints. The named mechanisms below are
screened source mechanisms and negative comparators, not survivor cards.

### NEG-M: Mahler or functional-equation constants

**Source-pinned mechanisms.** M1 starts with a primitive real-valued
`k`-regular sequence: nonnegative digit matrices `B_a`, positive
`B=sum_a B_a`, and a finite-dimensional `k`-kernel representation. It obtains
weak limits of pure-point measures and an exact Fourier matrix recursion. Under
the unique-dominant-eigenvalue and joint-spectral-radius gap, Theorem 5 gives
Holder exponent every `alpha<log_k(rho/rho_*)` for its limit function `F_f`;
the source warns that those assumptions alone do not make `F_f` a distribution
function. M2 starts from the exact base-`3/2` block substitution recurrence; its
limiting filtered frequencies obey a 2-adic operator whose two-step squared
`L2` contraction is at most `20/27`.

**Nearest branches.** M1 is nearest T133's screened `C-REG` language and T104's
Mahler/fixed-point comparators. M2 is nearest T115's substitution/Riesz branch
and T131's exact symbolic incidence constructions. Neither imports those
reports' deductions.

**First failed hypotheses.** No source proves that even one nontrivial
indicator

```text
j |-> 1[piCylinderCode(ell,j)=b]
```

has a finite 10-kernel, let alone representations uniform in growing `ell`.
Thus M1 fails before its primitivity or spectral-gap tests. M2's recurrence is
derived from the exact identities of its base-`3/2` word; no finite
desubstitution recurrence is known for the prescribed decimal path of pi.

**Quantitative screen.** M1's Corollary 2 propagates each fixed Fourier
frequency and Theorem 5 controls a limiting distribution function; neither
provides a prefix-length rate for the T7 bound or the simultaneous boundary and
Fourier budgets in T107. M2 obtains limiting one-symbol frequencies by
subsequence compactness and uniqueness. The constant `20/27` contracts the
limiting depth operator, not finite-prefix pair energy, so it cannot be placed
in `(T7-screen)` or `(T107-screen)`.

**Classification.** Both theorems are inapplicable at their first structural
hypotheses. No theorem or proposed transfer is falsified by the fixed-pi
failure. The domain has no survivor.

### NEG-F: arithmetic or fractal Fourier decay

**Source-pinned mechanisms.** F1 gives an explicit base-10 homogeneous
self-similar Rajchman measure whose transform along tetrational frequencies is
at least inverse-log-log scale, and constructs a monotone nonsummable shrinking
target law missed by every point in its support. F2's principal Theorem 1.5
uses an affinely irreducible self-similar IFS with a Diophantine log-contraction
ratio to obtain polylogarithmic Fourier decay. Its proof architecture uses
L2-flattening and separation of dynamically sampled frequencies; T136 does not
treat the separately attributed flattening theorem reproduced in F2 as a new
primary-source result.

**Nearest branches.** Both are nearest T104's ambient-measure Fourier branch.
F1 sharpens that branch negatively by showing that qualitative Rajchman decay
alone has no useful rate. F2 adds arithmetic escape from a sparse bad-frequency
set but retains the same ambient-measure/named-fiber gap.

**First failed hypotheses.** Direct substitution of `delta_pi` fails F2's
affine non-concentration, and `|delta_pi_hat(xi)|=1`. For the natural decimal IFS
all contraction ratios are `1/10`, so every log-ratio is exactly `1`, violating
F2's Diophantine inequality at `p/q=1`. Using F1's measure instead would require
placing pi in its support and then proving the needed named-fiber behavior;
neither is supplied.

**Quantitative screen.** For

```text
S_J(c;x)=sum_(0<=j<J) exp(2*pi*i*c*10^j*x),
```

an ambient probability measure satisfies the exact identity

```text
integral |S_J(c;x)|^2 dmu(x)
 = J + 2*Re sum_(0<=j<i<J) mu_hat(c*(10^i-10^j)).
```

This is an average over `x`; `(T10-screen)` evaluates one prescribed `x=pi`
and adaptive `c=h(10^r-1)`. F1 supplies no rate capable of the substitution and
F2 supplies no theorem locating pi outside its sparse bad-frequency sets. No
adjacent T28 compatibility or T107 boundary estimate follows.

**Falsification boundary.** F1 Theorem 1.7 genuinely falsifies only the broad
principle "qualitative Rajchman decay for a self-similar law forces every
divergent monotone base-10 shrinking-target law." It does not estimate pairwise
near returns and does not falsify A1, collision-C1, T10 cancellation for pi, or
T107's conditional premise. F2 is merely inapplicable.

**Classification.** The domain has no survivor.

### NEG-X: short structured exponential sums

**Source-pinned mechanisms.** In X1, specialize Theorem 2.4 to dimension one,
prime field `F_p`, scalar matrix `A=(10)`, nonzero numerator `a`, and
`tau=ord_p(10)`. Then `kappa_1=1/4` and `t=tau`, so the complete sum is bounded
by

```text
tau^(1/2)*p^(1/4)                  if tau>p^(1/2),
tau^(3/4)*p^(1/8)                  if tau<=p^(1/2).
```

Remark 2.6 extends this by completion to an initial segment with an additional
`log p`. X2 gives, for fixed `epsilon>0`, polynomial `f` of degree `d>=1`, and
a complete subgroup `G` of order `tau>=p^(3/7+epsilon)`,

```text
|sum_(x in G) exp(2*pi*i*f(x)/p)| <= C*tau*p^(-eta_d(epsilon)).
```

For `d=1,2`, `eta_d(epsilon)=7*epsilon/27`.

**Nearest branches.** X1 is nearest T118's private-prime-power prescribed
numerator and logarithmic-length audit. X2 is nearest T117's complete
finite-field pattern/character-sum model. Neither supplies a new route around
the previously recorded prefix barrier.

**Quantitative screen.** In the most favorable logarithmic-period branch
`tau asymp J asymp log p`, X1's completed second bound is

```text
p^(1/8)*(log p)^(7/4),
```

whose ratio to the trivial `J asymp log p` is
`p^(1/8)*(log p)^(3/4)->infinity`. This is noninformative at the T10 length,
not evidence that the actual sum is large. For X2, identifying the full subgroup
with `J asymp log p` violates `tau>=p^(3/7+epsilon)` for large `p`; if `tau`
satisfies the theorem and only the first `J` powers are wanted, the prefix is
not the complete subgroup.

There is also a genuine elementary falsification of a different uniform claim.
For any modulus `q` and numerator `a=1`,

```text
|sum_(j<J) exp(2*pi*i*10^j/q)-J|
 <= 2*pi*(10^J-1)/(9*q).
```

Hence uniform `o(J)` cancellation for every numerator is false when
`J<=(1-delta)log_10(q)`. T10 does not demand every numerator, so this does not
falsify its prescribed adaptive coefficients.

**Classification.** X1 is applicable as a theorem but quantitatively useless;
X2 is inapplicable to a logarithmic prefix. Neither outcome falsifies
cancellation for the actual prescribed sum. The domain has no survivor.

## 7. Survivor and successor ledger

No screened mechanism survives both its source hypotheses and one named
fixed-pi quantitative screen. Accordingly there is no conjectural fixed-pi
transfer premise to promote, no retained normalized fingerprint, and no bounded
successor. Source-retrieval and comparison succeeded, so the negative cards are
mathematical applicability conclusions rather than retrieval blockers.

```text
RETAINED_FINGERPRINTS: none
CONJECTURAL_FIXED_PI_TRANSFER_PREMISES: none
SUCCESSOR: none
FIXED_PI_CLAIM: none
C1_CLAIM: none
C2_CLAIM: none
NOVELTY_CLAIM: none
```

## 8. Replay

From a directory containing only the delivered artifacts, run

```bash
python3 verify_t136.py
sha256sum -c SHA256SUMS
```

The verifier checks local hashes, the six-source/three-domain ledger, PDF
theorem anchors, prior-evidence archive membership, T130--T135 delta/status
anchors, all count
and scope markers, the logarithmic exponent substitutions, and the unique
endpoint. It does not promote finite string or arithmetic checks into proof of
any universal assertion.

OVERALL_VERDICT (1/1): close
