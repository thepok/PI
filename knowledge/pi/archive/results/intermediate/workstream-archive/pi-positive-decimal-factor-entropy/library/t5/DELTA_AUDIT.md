# T5 source-pinned delta audit

Status: `literature-checked` on 2026-07-23 for the bounded corpus in
`SOURCE_MANIFEST.md`.

This artifact is an applicability audit. It proves no unconditional statement
about the decimal factors, collision energy, lacunary orbit, or Fourier
coefficients of pi. `DOES NOT APPLY` means that the cited result does not
establish the target with all hypotheses matched; it does not mean the target
is false. Finite evidence and heuristic expectations are not used.

## 1. Exact Targets and Quantifier Matrix

The immutable canonical statement has SHA-256
`a70dd741b27595aeb3dfc902b5e201579fed6bae24e2191f58c5ac64a22939e6`.
The accepted formal definitions below fix all otherwise ambiguous quantifiers.

| Target | Exact quantifiers and object | Non-substitutable clauses | Formal locator |
|---|---|---|---|
| C1, positive decimal factor entropy | There exist one real `eta>0` and one integer `N>=1` such that for every integer `n>=N`, `p_pi(n)>=10^(eta*n)`. | Fixed pi; base 10; all contiguous factors at arbitrary positions; one eta; every sufficiently large n. Superlinear or superpolynomial complexity is not enough. | T1 `CanonicalEntropy.lean`, `EventuallyExponentialFactorGrowth`, lines 135-144, and pi specialization lines 336-346. |
| C2, exponential collision energy | There exist one real `eta>0` and one integer `n0>=1` such that for every `n>=n0` there exists `M>=1` with `E_pi(n,M)<=M^2*10^(-eta*n)`. | One eta before all n; `M` may depend on n; ordered finite-prefix collision energy; exponential decay in factor length n. | T2 `T2ExponentialCollisionCriterion.lean`, lines 34-42. T2 lines 120-143 machine-check only `C2 -> C1`. |
| HFE, weighted ordinary-orbit hypothesis | For every real `A>0` and `epsilon>0`, there is `nstar>=1` such that every `n>=nstar` has some `N>=1` with `W(n,ceil(A*n),N,pi)<epsilon*N^2/n`, where `W=sum_(1<=h<=H) min(2*10^(-n)+1/(H+1),1/(pi*h))*|sum_(j<N)e(h*10^j*pi)|^2`. | Fixed pi; all frequencies through a linear cutoff simultaneously; exact weights; polynomial `1/n` saving. | `T10PiWeightedFourierReduction.lean`, weights lines 70-78, HFE lines 1085-1097. Lines 1125-1226 prove only HFE implies the older polynomial near-return condition. |
| MF, multiplicity/Fourier obstruction | Assuming literal failure of C1, for every `epsilon>0`, all sufficiently large n have `p_pi(n)<10^(epsilon*n)` and some nonzero additive character on `ZMod(10^n)` with the T3 cell-support lower bound. For that character, every positive prefix covering all occupied n-cells has either normalized cell-label prefix coefficient at least half the cell-support coefficient or multiplicity defect at least half that coefficient. | Conditional on failure of C1; character may depend on n; uniform distribution on distinct occupied cells; covering prefix; cell-label coefficient, not an ordinary `e(h*10^j*pi)` sum; no unconditional choice of branch. | T3 `FiniteFourierObstruction.lean`, lines 471-509; T4 `T4FinitePrefixMultiplicityTransfer.lean`, lines 293-334. |

### Ambiguities resolved

1. The symbol C1 here always means positive exponential factor complexity,
   not the older superlinear or collision predicates in adjacent programs.
2. C2 here always means exponential `10^(-eta*n)` collision decay. The older
   lacunary condition `Q_pi(n,N)<N^2/(C*n)` is only polynomial in n.
3. HFE uses ordinary time-indexed lacunary sums. MF uses characters of finite
   decimal cell labels and includes a multiplicity-defect alternative. No
   transfer between these coefficients is assumed.
4. Almost every initial point never means the named point pi. A conull set can
   omit any prescribed singleton.
5. A result in base 2 or 16 is not transferred to base 10.
6. An asymptotic or finite result about selected n is not substituted for
   every sufficiently large n.

## 2. Accepted Formal Bridges: Scope Only

These rows explain which logical reductions are already machine-checked. An
`APPLIES` verdict here means only that the conditional implication has the
right formal types; it does not discharge its premise.

| Result | Verdict | What it establishes | What remains unproved |
|---|---|---|---|
| T1 positive entropy equivalence | **APPLIES (equivalence only)** | `0<h_10(pi)` is equivalent to exact C1. | Neither side. |
| T2 exponential collision criterion | **APPLIES (conditional bridge only)** | Exact C2 implies exact C1 with the same eta and cutoff. | C2 for pi. |
| T3/T4 obstruction | **APPLIES (conditional obstruction only)** | Literal failure of C1 implies the stated cell-label coefficient and prefix multiplicity dichotomy. | Failure of C1, an unconditional branch, and any orbit-sum transfer. |
| T10 weighted reduction | **APPLIES only to the older polynomial target; DOES NOT APPLY to current C2 or C1** | HFE implies `Q_pi(n,N)<N^2/(C*n)` for each C and all large n with an n-dependent N. | HFE itself; exponential `10^(-eta*n)` decay; positive entropy. |

The last row is the central delta from the adjacent factor-complexity program:
even a proof of its accepted HFE premise would yield superlinear factor
complexity, not the exponential C2 required here.

## 3. Literature Hypothesis Matrix

Every source result cited by this audit appears exactly once below. Each target
cell has an explicit `APPLIES` or `DOES NOT APPLY` verdict. There is no
unconditional `APPLIES` cell in this bounded literature matrix.

| ID and exact result | Literal scope | C1 | C2 | HFE | MF | First decisive blocker and retained label |
|---|---|---|---|---|---|---|
| AB07, Theorem 1, pp. 549-550 | For every irrational algebraic real in each integer base, `liminf p(n)/n=+infinity`. | **DOES NOT APPLY.** Pi is transcendental, not algebraic; the conclusion is only superlinear and can have zero entropy. | **DOES NOT APPLY.** No collision-energy statement. | **DOES NOT APPLY.** No orbit sums. | **DOES NOT APPLY.** No cell-label coefficient or multiplicity statement. | Algebraic-only theorem; false central hypothesis for pi. |
| EG55, EG-I main theorem p. 65 with proof completed in EG-II Sections 3-4 pp. 77-84 | Under a Hadamard gap, the normalized lacunary sum has LIL limsup 1 for Lebesgue-almost every initial point. For fixed h use frequencies `h*10^j`. | **DOES NOT APPLY.** No fixed-pi factor bound or exponential transfer. | **DOES NOT APPLY.** The published conclusion is not at pi and does not itself state collision energy. | **DOES NOT APPLY.** All HFE frequency and existential-N quantifiers can otherwise be met on one conull set, but no theorem puts pi in that set. | **DOES NOT APPLY.** Ordinary orbit sums are not T3/T4 cell-label coefficients and no defect branch is bounded. | Almost-everywhere; first HFE failure is fixed point. |
| SZ47, result (vi), p. 337 | For a Hadamard-gap series with complex coefficients, put `C_N=(1/2*sum_(k<=N)|c_k|^2)^(1/2)`. If `C_N->infinity` and `c_N=o(C_N)`, then the normalized real and imaginary partial sums converge jointly to the standard two-dimensional Gaussian distribution as the initial variable ranges over any fixed positive-measure set. | **DOES NOT APPLY.** No named-pi factor theorem. | **DOES NOT APPLY.** No named-pi pair count or energy. | **DOES NOT APPLY.** Distribution over initial points gives neither a pointwise pi bound nor simultaneous growing-frequency HFE. | **DOES NOT APPLY.** Coefficients weight time terms, not the MF cell-support distribution or multiplicity defect. | Metric distribution theorem, not pointwise. The source also states an analogous tail version under separate tail hypotheses; that version is not used here. |
| PH75-T1, Theorem 1, pp. 241-242 | For an integer sequence with `n_(j+1)/n_j>=q>1`, for almost every x, `32^(-1/2)<=limsup N*D_N({n_j*x})/sqrt(N*log log N)<=C`, where `C<=166+664/(sqrt(q)-1)`. | **DOES NOT APPLY.** No fixed-pi factor conclusion. | **DOES NOT APPLY.** No fixed-pi discrepancy or collision bound. | **DOES NOT APPLY.** With `n_j=10^(j-1)` and finite intersections over h, the asymptotic scale would suffice for metric HFE, but the theorem does not apply at pi. | **DOES NOT APPLY.** Ordinary discrepancy has no cell-label or multiplicity-defect conclusion. | Almost-everywhere discrepancy theorem; first blocker is fixed pi. |
| PH75-D, deterministic inequality (3.9), p. 250 | For every finite point sequence, an exponential sum is bounded by `sqrt(32)*N*D_N`; the note improves the coefficient to 4. | **DOES NOT APPLY.** It supplies no small discrepancy and no factor-complexity conclusion. | **DOES NOT APPLY.** No fixed-pi discrepancy bound strong enough for exponential collision decay is supplied. | **DOES NOT APPLY.** The inequality is valid at pi, but HFE still requires an unproved simultaneous fixed-pi discrepancy estimate. | **DOES NOT APPLY.** It concerns ordinary orbit sums and has no cell-label or multiplicity transfer. | Conditional deterministic bridge; missing quantitative fixed-pi discrepancy. |
| FU08, theorem and Corollary (4), pp. 155-156 | For fixed `theta>1` and almost every x, geometric-progression discrepancy has an exact LIL constant. Corollary (4) prints `Sigma_theta=(1/2)*sqrt((p+1)*p*(p-2)/(p-1)^3)` when `theta=p` is an even integer `p>=4`. The audit's substitution `p=10` gives `(1/2)*sqrt(11*10*8/9^3)=sqrt(220)/27`; that base-10 value is derived arithmetic, not a verbatim source quote. | **DOES NOT APPLY.** No fixed-pi factor theorem. | **DOES NOT APPLY.** No fixed-pi energy bound. | **DOES NOT APPLY.** Combined with PH75 it would give the metric HFE analogue, but the theorem does not identify pi as a good point. | **DOES NOT APPLY.** Ordinary discrepancy does not select T3's varying finite-cell character or control T4's defect. | Almost-everywhere, exact base 10 after the displayed substitution; first blocker is fixed pi. |
| RZ99, Corollary 3 via Theorem 1 and Proposition 2, p. 284 | For every integer `g>=2`, `{alpha*g^j}` has Poisson pair correlation for almost every alpha. | **DOES NOT APPLY.** The theorem does not apply at alpha=pi. | **DOES NOT APPLY.** Its conclusion would be sufficient at pi, but the published quantifier is almost every alpha. | **DOES NOT APPLY.** Pair correlation is not the exact positive weighted energy inequality. | **DOES NOT APPLY.** No uniform-support cell character or multiplicity-defect branch. | Almost-everywhere. This is the closest direct route to C2; the exact conditional reduction is in Section 4. |
| RZ02-CORR, Theorems 1.1-1.2, pp. 1-3 | Every lacunary integer sequence has Poisson local correlations for almost every multiplier; one full-measure set handles all correlation orders and smooth compactly supported tests. | **DOES NOT APPLY.** No fixed-pi membership. | **DOES NOT APPLY.** The pair-correlation specialization would suffice only after the missing fixed-pi premise and standard sharp-count majorization. | **DOES NOT APPLY.** Correlation statistics are not the exact HFE weighted sum. | **DOES NOT APPLY.** No MF coefficient identification or defect control. | Almost-everywhere; smooth local statistic. |
| RZ02-MS, Lemma 3.1 pp. 10-11 and Proposition 4.1 p. 11 | Mean and `L^2(d alpha)` variance bounds for smoothed local correlation statistics. | **DOES NOT APPLY.** Parameter averages do not evaluate a singleton. | **DOES NOT APPLY.** Mean-square control over alpha is not a fixed-pi energy bound. | **DOES NOT APPLY.** Different quadratic form and averaged parameter. | **DOES NOT APPLY.** No finite-cell support or multiplicity statement. | Parameter mean-square; not pointwise. |
| BBP97, Theorem 1 p. 3 and digit algorithm Section 3 pp. 7-8 | Unconditional base-16 identity and random-access hexadecimal digit computation for pi. | **DOES NOT APPLY.** Digit extraction is not decimal factor distribution, and the base is wrong. | **DOES NOT APPLY.** No decimal collision estimate. | **DOES NOT APPLY.** No base-10 lacunary cancellation estimate. | **DOES NOT APPLY.** No decimal cell-support or multiplicity theorem. | Unconditional fixed pi, but base-16 computation only. |
| BC02, Hypothesis 3.1 and conditional Theorem 3.3, p. 531 | Under the unproved Bailey-Crandall Hypothesis A, pi is 2-normal. | **DOES NOT APPLY.** The premise is unproved and the conclusion is base 2, not base 10. | **DOES NOT APPLY.** No decimal collision estimate or cross-base transfer. | **DOES NOT APPLY.** No decimal orbit HFE conclusion. | **DOES NOT APPLY.** No decimal finite-cell/multiplicity conclusion. | Conditional and wrong base. |
| ZZ20, bound p. 407 and Propositions 7-8 pp. 417-418 | The irrationality measure of the named number pi is at most `7.103205334137...`. | **DOES NOT APPLY.** Irrationality measure does not imply exponential factor complexity; transcendental linear-complexity examples rule out such a general inference. | **DOES NOT APPLY.** It separates individual phases but gives no aggregate collision-energy upper bound. | **DOES NOT APPLY.** Direct termwise phase separation leaves the weighted sum on the `N^2` scale, not `N^2/n`. | **DOES NOT APPLY.** No cell-support Fourier upper/lower transfer and no multiplicity control. | Fixed pi and unconditional, but individual rational separation rather than collective cancellation. |

## 4. Concrete Conditional Reduction from Fixed-Pi Pair Correlation

This section records a reduction, not an application of RZ99 or RZ02. Apply
the setup of RZ99 Theorem 1 and Proposition 2 to the explicit integer sequence
`a(x)=10^(x-1)` for `x=1,2,...`; its first M terms are exactly the zero-based
powers `10^0,...,10^(M-1)` used by formal `Q_pi`. Assume the resulting Poisson
pair-correlation conclusion at the named multiplier pi. At scale `s=1`, for
all sufficiently large sample sizes M, the ordered off-diagonal count at
distance at most `1/M` is at most `3M`. Adding the M diagonal pairs gives at
most `4M` ordered pairs.

For a factor length n, choose `M=10^n`. Then `1/M=10^(-n)`, and the strict
near-return count is at most the non-strict pair count, so

```text
E_pi(n,M) <= Q_pi(n,M) <= 4M = 4*10^n.
```

Choose `eta=1/2`. For every `n>=2`,

```text
4*10^n <= 10^(3n/2)
         = M^2 * 10^(-eta*n).
```

After enlarging the cutoff to the pair-correlation threshold, this is exact
C2 with one eta, every later n, and `M=10^n`; accepted T2 would then give C1.
The published RZ theorems do **not** supply the fixed-pi premise, so this
calculation is a conditional reduction only. It identifies a concrete missing
hypothesis rather than promoting an almost-everywhere theorem.

## 5. Why the Weighted and MF Routes Do Not Merge Automatically

### Weighted HFE versus exponential C2

Accepted T10 uses a linear frequency cutoff and proves a bound of order
`N^2/(C*n)` for a near-return count. Current C2 requires
`N^2*10^(-eta*n)`. No fixed positive eta can satisfy
`1/(C*n)<=10^(-eta*n)` for all large n. Therefore the accepted implication
chain from HFE stops at the older superlinear factor-complexity target. It
cannot be cited as progress on current C1 without an exponentially stronger
analytic input.

The metric EG and FU theorems are strong enough to instantiate accepted HFE
for almost every initial point because HFE chooses N after n. That fact does
not repair either gap: it does not identify pi, and accepted HFE still has
only the polynomial target.

### Ordinary orbit sums versus the MF obstruction

T3 Fourier-transforms the uniform measure on distinct occupied decimal
n-cells. T4 compares that coefficient to a time average of truncated cell
labels and an `l1` multiplicity defect, under a prefix-coverage hypothesis.
EG, PH, FU, and SZ concern ordinary phases `e(h*10^j*x)`. None of their cited
theorems identifies those phases with the varying additive character selected
by T3, controls truncation uniformly in n, proves prefix coverage, or controls
the multiplicity defect. Consequently no side of the T4 disjunction is
settled by the audited literature.

## 6. Frontier Verdict

Within this bounded, source-pinned corpus:

1. **No cited theorem applies unconditionally to C1 or C2.** AB07 has the
   wrong algebraicity hypothesis and only a superlinear conclusion. BBP and
   Bailey-Crandall do not supply decimal distribution.
2. **No cited theorem proves fixed-pi HFE.** The strongest matching lacunary
   sum and discrepancy estimates are almost-everywhere. PH75 is only a
   deterministic bridge conditional on an unproved fixed-pi discrepancy
   estimate. Even HFE would not prove current exponential C2.
3. **No cited theorem resolves either MF branch.** The coefficient objects and
   multiplicity hypotheses do not match ordinary lacunary sums.
4. **The strongest concrete missing fixed-pi hypothesis for this agenda is a
   Poisson pair-correlation upper bound for `{10^j*pi}`.** The exact reduction
   above would give C2 with `eta=1/2`, hence C1. The retained RZ results prove
   this only for almost every multiplier.
5. **The strongest unconditional fixed-pi Diophantine input retained is the
   ZZ20 irrationality-measure bound.** It supplies individual phase
   separation, not aggregate pair sparsity or Fourier cancellation, and
   therefore does not support C1 or C2.

These statements are a `literature-checked` frontier verdict for the declared
corpus. They are not a proof that no other theorem exists, not a proof or
disproof of C1/C2, and not a novelty claim.
