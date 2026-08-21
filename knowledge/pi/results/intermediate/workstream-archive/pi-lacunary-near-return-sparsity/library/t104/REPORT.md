# T104: bounded cross-domain mechanism scout

Search date: 2026-08-09 UTC.

Claim labels: the source statements quoted below are `literature-checked`
against the twelve delivered primary PDFs and their exact theorem locators.
All comparisons, rejection calculations, and transfer implications newly made
in this report are `proof sketch`. `verify_t104.py` performs exact integrity and
arithmetic checks; it is not evidence for a universal mathematical claim.

This report proves no statement about pi, canonical C1, or C2. Every sourced
theorem concerns a related model or an almost-everywhere class. Every displayed
fixed-pi premise is explicitly an additional unproved premise, not a conclusion.

```text
PRIMARY_SOURCE_COUNT: 12
SEARCHED_DOMAIN_COUNT: 4
RETAINED_FINGERPRINT_COUNT: 4
TERMINAL_VERDICT_COUNT: 1
SUCCESSOR_COUNT: 0
```

## 1. Immutable statement and normalized scope

The delivered `canonical_statement.txt` is a byte-exact copy of the local
canonical statement and has SHA-256

```text
cbf56699b651aeb69301265763e38da44feb59c6fd955d2280887e8c06c6a2f8
```

For integers `n,N >= 1`, the canonical count is

```text
Q_pi(n,N) = #{(i,j): 0 <= i,j < N and
                       ||(10^i-10^j)pi||_(R/Z) < 10^(-n)}.
```

Pairs are ordered, all `N` diagonal pairs are included, the circle cutoff is
strict, and the open quantifier order is

```text
for every integer A >= 1
  there exists n0 >= 1
    such that for every n >= n0
      there exists N >= 1 with A*n*Q_pi(n,N) <= N^2.
```

Thus `N` may depend on `A,n`. None of the literature below changes this
statement or establishes it. In particular, a theorem for almost every
parameter, a self-conformal measure, a Mahler value, another fixed point,
off-diagonal pair correlation, scalar return to zero, or bounded data is an
A13/A14 related model only. Such a theorem is not a result about pi, C1, or C2.

## 2. Bounded clean-context protocol

Four independent lanes were searched, with a hard stop after three primary
sources in each lane:

1. Mahler and functional-equation constants;
2. restricted-denominator approximation;
3. arithmetic and fractal Fourier decay;
4. short structured exponential sums and lacunary correlations.

All twelve sources are dated 2020-2026 by preprint or publication date. The
search then stopped. The accepted local library was consulted only after the
source claims were normalized, to test duplication and identify the nearest
closed branch. Exactly four fingerprints were retained for full cards. No
candidate was added to fill the cap.

The primary files are byte-pinned in Section 3 and in `SHA256SUMS`. Retrieval
used the displayed arXiv or HAL primary URL. Exact locators use theorem,
corollary, proposition, lemma, equation, and printed-page identifiers, so the
claims can be checked directly in the delivered PDFs.

## 3. Primary-source ledger

| ID | Domain | Primary identifier and URL | Exact inspected locator | Delivered PDF SHA-256 | Use |
|---|---|---|---|---|---|
| S1 | Mahler | Andrew Rajchert, *On the Irrationality Exponents of Mahler Numbers*, arXiv:2411.10733v1, <https://arxiv.org/abs/2411.10733> | Theorem 3.13, Chapter 3 Section 3.2 | `d0d407758686605a1e6bcdbc5631cad5bb3d6cf46781cc4ded1d6ce8cbb94760` | screened |
| S2 | Mahler | Adamczewski-Bell-Smertnig, *A height gap theorem for coefficients of Mahler functions*, arXiv:2003.03429v2, DOI 10.4171/JEMS/1244, <https://arxiv.org/abs/2003.03429> | Theorem 1.2, printed p. 4 | `c70932ece1c4cdcf5a62b39f91103c98841b3b958f3f622d58550322b9469353` | screened |
| S3 | Mahler | Poulet-Rivoal, *Radial behavior of Mahler functions*, HAL hal-03703010v1, DOI 10.1142/S1793042124501070, <https://hal.science/hal-03703010v1> | assumptions H1-H6, Theorem 2 and equations (1.8)-(1.10), printed pp. 5-7 | `05bfb82585d161d043460b92237931729b91bf2ebb1636cd52d3ead62a26421f` | F1 |
| S4 | restricted denominator | Chance Sanford, *A Note on Diophantine Approximation with Restricted Denominators*, arXiv:2606.02620v1, <https://arxiv.org/abs/2606.02620v1> | Definition 1 and Theorems 3-4, printed pp. 2-3 | `4012d480b3c3aff5d2a36c4cc92d2e57027baa9b64454b77edfcaf3b2fb45b0b` | screened |
| S5 | restricted denominator | Hauke-Ramirez, *Twisted approximation with restricted denominators*, arXiv:2508.01433v1, <https://arxiv.org/abs/2508.01433v1> | Theorem 2, printed p. 3; Lemma 8, printed p. 6 | `fae15d1d5e0d869a0cf1cebd406da06087010f96466a6012531acd441647ab89` | F2 |
| S6 | restricted denominator | Wang-Li-Li, *Uniform Diophantine approximation with restricted denominators*, arXiv:2302.03923v2, <https://arxiv.org/abs/2302.03923v2> | definition before (1.2), Theorem 1.1 and equation (1.4), printed pp. 5-6 | `278dca3331322b1a64d34fb04651e131e7eb3a6482b5be5b69e9db29d39670ad` | screened |
| S7 | fractal Fourier | Varju-Yu, *Fourier decay of self-similar measures and self-similar sets of uniqueness*, arXiv:2004.09358v2, DOI 10.2140/apde.2022.15.843, <https://arxiv.org/abs/2004.09358> | Theorem 1.5, Corollary 1.8, Theorem 1.10, printed pp. 3-5 | `4f8fe4bb024df9d7c0c804f93f261f3c4f21cc4d9410f9984804ad60594e7fad` | screened |
| S8 | fractal Fourier | Sahlsten-Stevens, *Fourier transform and expanding maps on Cantor sets*, arXiv:2009.01703v5, DOI 10.1353/ajm.2024.a932433, <https://arxiv.org/abs/2009.01703> | total nonlinearity (4), Theorem 1.1, printed pp. 3-4 | `ba4878034d08a46c0e5cad13b4028922ba1ae058f0a55d11f111c4d8706693bf` | F3 |
| S9 | fractal Fourier | Algom-Rodriguez Hertz-Wang, *Spectral gaps and Fourier decay for self-conformal measures on the plane*, arXiv:2407.11688v3, DOI 10.1090/tran/9507, <https://arxiv.org/abs/2407.11688> | Theorem 1.1, printed pp. 2-3 | `b3eb5abb5f904ffaed7d0e496cc096ff686a8d52f7860876ded2ebd66c0a7d9d` | screened |
| S10 | structured sums | Rudnick-Technau, *The metric theory of the pair correlation function of real-valued lacunary sequences*, arXiv:2001.08820v1, DOI 10.1215/00192082-8720506, <https://arxiv.org/abs/2001.08820> | Theorem 1.1, printed p. 2; Proposition 4.2 | `364164f781a31ad5267b3c43d91b0593418744e8ac9073407e24581981b887b2` | screened |
| S11 | structured sums | Chaubey-Yesha, *The distribution of spacings of real-valued lacunary sequences modulo one*, arXiv:2108.00431v1, <https://arxiv.org/abs/2108.00431v1> | Theorem 1 and Proposition 2, printed pp. 3-4 | `b660b086d52ecaf9d2e7abe13bcc306765dbc1166076ccb9ddbb14d1461e7e54` | screened |
| S12 | structured sums/fractal Fourier | Baker-Banaji, *Polynomial Fourier decay for fractal measures and their pushforwards*, arXiv:2401.01241v2, DOI 10.1007/s00208-025-03091-z, <https://arxiv.org/abs/2401.01241v2> | Theorem 1.2, printed p. 4; Properties A-C, Proposition 2.5 and Theorem 2.7, printed pp. 13-15 | `f07b9e579360cff6843fccb526086d27ea454925d6ed46d297fff274ca5689e6` | F4 |

The source IDs map to delivered files as follows:

```text
S1  rajchert-2411.10733.pdf
S2  adamczewski-bell-smertnig-2003.03429.pdf
S3  poulet-rivoal-hal-03703010v1.pdf
S4  sanford-2606.02620v1.pdf
S5  hauke-ramirez-2508.01433v1.pdf
S6  wang-li-li-2302.03923v2.pdf
S7  varju-yu-2004.09358.pdf
S8  sahlsten-stevens-2009.01703.pdf
S9  algom-rodriguez-hertz-wang-2407.11688.pdf
S10 rudnick-technau-2001.08820.pdf
S11 chaubey-yesha-2108.00431v1.pdf
S12 baker-banaji-2401.01241v2.pdf
```

## 4. Local obstruction memory and mandatory exclusions

The comparison memory is not used as a mathematical premise. It records
semantic warnings and verification levels. The consulted copy is
`t89/SEMANTIC_OBSTRUCTION_MEMORY.md`, SHA-256
`aa8b0f84010f2850807e383e21f45dcb9c0dc548b5e22e0c3c4cd2779528f76f`.
It warns, with mixed verification levels, that scalar irrationality, exact
regrouping, isolated rows, rational order, invariant/model measures, and finite
certification do not by themselves produce adaptive fixed-pi cancellation.

### 4.1 Mandatory named exclusions

| Excluded work | Local status used | Normalized excluded fingerprint | Inspection pin |
|---|---|---|---|
| T95/T98 universal charging | both are unverified `proof sketch` notes; T95 gives exact-word charging and T98 argues a conditional transport | local exact-word overlap charging; no direct reversal to a Vaaler majorant and no fixed-pi long-sector bound | T95 report SHA `08baad91851c1d25ceaa82f86cbe8b728ca2c063f31f01f83c5fa96aea45d8cb`, Sections 2-4 and 7; T98 SHA `b6b8d30499543fadf5be200b85afe3929dcba5b7a7d96061476965060c589f57`, Sections 4-8 |
| T100 universal charging | active/unavailable in the supplied library | excluded by agenda without inferring its content from T95/T98 | no local report; not inspected |
| T93/T96/T99/T102 Stoneham | source audits are literature-checked where stated; mathematical developments remain unverified `proof sketch` | rational skeleton, repeated prime-power residues, exact order, and a tail below the pair scale | report SHAs `2ff685b2...`, `de8940fd...`, `9778fd0f...`, `49a63d00...`; each report's final fingerprint/boundary section |
| T91/T94/T97/T101 paperfolding | source statements literature-checked where stated; new collision developments are unverified `proof sketch` and bounded replays are `experiment` | valuation/odd-part automatic word, canonical representatives or exact multiplicity profiles, but no conserved overlapping decimal row or metric carry map | report SHAs `a684f159...`, `f399dfac...`, `fb3c58a4...`, `ddd24794...`; each report's mechanism and transfer section |
| T103 Toeplitz | active/unavailable in the supplied library | excluded without inspection or proxy inference | no local report; not inspected |

The ellipses in this table abbreviate hashes whose full values appear in the
local accepted-library manifests; the exact files and full hashes inspected in
this run are listed here for audit:

```text
T93  2ff685b20920f5a2d71db2b8a300ce8c2762152c3d4b2c59236b160ed812f8ae
T96  de8940fd7927a20d88626cec7ae8b411cd2788c1fdecb762496a72c8f18019aa
T99  9778fd0fdc3151b0e3f8888afdb1d1049347e926d266f2981e7daa3bc44af2b4
T102 49a63d0003102728766a41e026400f3bc69e9baeb42e66338510bcbecc1d6304
T91  a684f15960a176f37ee2e8e853313e05e0e2f8de9674be2fcd744f59fe62573e
T94  f399dfac1990b3cc4a6c9e69127a1ceff22356c6b656ec2e3a1b9045be6efa10
T97  fb3c58a436d173902ccf3577dc02d1702403f681d6cc08a39481e1c73cd31a8e
T101 ddd24794d6e6795a4aa466819782aa63a6578d70746ce4d592bb18ef644c243e
```

No retained fingerprint below uses charging, Stoneham arithmetic,
paperfolding recursion, or Toeplitz structure.

### 4.2 T63/T68/T78-T90 non-duplication ledger

Rows marked `proof sketch` are comparison history only, never discharged
premises.

| Prior branch and level | Normalized fingerprint and recorded terminal obstruction | Comparison with F1-F4 |
|---|---|---|
| T63, `literature-checked` applicability audit, report SHA `28e7bdc2...` | pi series/digit algorithm or constructed constant -> rational phase; approximation and regrouping do not give adaptive cancellation | F1 is radial asymptotics, F2 is two-coordinate torus independence, F3 is derivative-cocycle nonlinearity, F4 is ambient-measure Fourier decay; none is a pi representation |
| T68, route-specific `machine-checked` obstruction plus note SHA `2f406533...` | corrected-Zudilin power-of-5 transient leaves no legal coprime tail at the required scale | no retained card removes a rational transient or invokes a rational tail |
| T78, `proof sketch`, SHA `26cc36a1...` | factorial truncation has square-root-modulus cost larger than the usable orbit length | no retained card uses factorial truncations |
| T79, `proof sketch`, SHA `7fb415a8...` | Machin specialization leaves a prime-power cofactor and no special-numerator sum bound | no retained card uses Machin arithmetic or numerator conductors |
| T80, `proof sketch`, SHA `df86924c...` | ideal order in a quadratic ring is not a real-character period | F1's radial periodicity is explicitly not called a circle-character period |
| T81, `proof sketch`, SHA `73b41980...` | scalar irrationality packing is exponentially too weak and supplies no compatibility | S1, S4, and S6 are screened as scalar routes; none is retained |
| T82, `proof sketch`, SHA `d06801d8...` | finite Chudnovsky certification carries expand and do not give coherent T64 rows | F3/F4 require new quantitative row or fixed-fiber premises and do not reuse finite certification |
| T83, machine-checked statistic interfaces plus unverified review discussion, report SHA `29a3cf71...` | exact equality is not all metric near returns; short control does not discharge the residual long sector | F2 states a full metric ball-intersection premise; F4 tests the exact T10 sum instead of exact-word equality |
| T84, rejected and unavailable | no usable exclusion theorem | no content inferred |
| T85, `proof sketch`, report SHA `06fc459a...` | valuation ties and empty coprime tails defeat the proposed rational transfer | no retained rational transfer |
| T86, `literature-checked` bounded audit, report SHA `16cff30f...` | semigroup density, Hata scalar approximants, and Wallis/Brouncker lengths miss named frontiers | F2's torus-lift is not semigroup density; F3/F4 are measure-cancellation models, not approximants |
| T87, mixed source audit and `proof sketch` synthesis, report SHA `a1232df0...` | charging leaves the long sector, restricted irrationality misses its threshold, and numerator-conductor bounds exceed the logarithmic budget | S1/S4/S6 are screened as repeats; F1-F4 use different normalized mechanisms |
| T88, `proof sketch`, report SHA `ca481e2d...`, not used as a premise | artificial invariant/model measures need a fixed-point or frequency-growing transfer rate | nearest boundary for F3/F4; their transfer premises retain that missing rate explicitly |
| T89, source audit plus `proof sketch` models, SHA `ad90a5a5...` | pure-power sparse constants can be maximally resonant; automatic recurrence can be collision-rich | nearest functional-equation warning for F1 and finite-state warning for screened S2 |
| T90, `literature-checked` corpus plus `proof sketch` transfers, SHA `730c5cda...` | explicit expanding-map points solve only their own sibling and fail the named-point discriminator | F2-F4 remain related-model statements and do not identify their points with pi |

Full omitted hashes in the preceding table are:

```text
T63 28e7bdc28628404532afcecda50ed954836df3eb7d6578315604907a7f10ad59
T68 2f406533d202ab9ec1bd570bdeb07ef51b5e24d69d8d3143add508414a333f14
T78 26cc36a18ea585d85d5e7f2c23e40df61bbb1ca94639541736531feb8074af4b
T79 7fb415a8140597f5a061b945df08eacc122e693d4998fafca98ff98aa641d800
T80 df86924ccf631ded30bb887e2d8a7ff6d0abfa2d5da5f0240221d526d85cbad5
T81 73b4198003d637e5b7277dbdfe05e4f2606613f8e906860243331a293dd3b77f
T82 d06801d820c9fd28286a48cdd7a2108a84db70de2561864979aa4dfc982f0ced
T83 29a3cf716da0e88cd1a0b51d2c63151b945a740cf773b256dfa9f282595ad760
T85 06fc459ab48d1d3cbe78a3038bdc76e20591ee86b7d243cba4a879a1e1fce2c7
T86 16cff30f045a0b5bf56aa80c98c63add19d55c6a5a5b126602d8c785e48e11fa
T87 a1232df07fa5c1ce31ba605217038c948bacd8f07f89b569b04da67cf1159078
T88 ca481e2d235955cbb137dc752a846a6de510cde1416cd0a2af308bb5a382b066
T89 ad90a5a5084f7ef19f4fce052ae99330f0cab9103f2942ee164d713de2a8b5b9
T90 730c5cdaf154bd375084a243fc82ebf6ab4ce2c1e234baf43515d4aaea34cfc0
```

## 5. Fixed-pi comparison thresholds

These are machine-checked local interfaces, not claims that their premises
hold for pi.

1. T7 finite-cylinder comparison: the local file
   `t7/FiniteCylinderEnergy.lean`, SHA
   `cac7b8da11c9369510e2e6e76b8bc74820b50ffe0285310475c7cf8ee1cfe91c`,
   lines 292-318 and 346-386, records the exact ordered, diagonal-inclusive
   finite-energy interface and canonical quantifiers.
2. T10 adaptive resonance: the canonical module
   `TheoryLib/PiLacunaryNearReturnSparsity/T10LongLagResonance.lean` and the
   byte-identical supplied comparison copy
   `knowledge_library/notes/t86/T10LongLagResonance.lean`, SHA
   `63ccfd2417aca055ef9071e03b70092acb1fee26a279db6c5c35c9295aa91947`,
   lines 829-894, has legal integers

```text
N = 16*A*n*K,  1 <= r < N,  J = N-r >= K,  1 <= h <= 256*A*n
```

and the resonance threshold

```text
|sum_(j<J) e(h(10^r-1)10^j*pi)| > J/(131072*A^2*n^2).
```

The half-budget cancellation discriminator used below is

```text
F10(A,n,r,h,J):
|sum_(j<J) e(h(10^r-1)10^j*pi)| <= J/(262144*A^2*n^2).
```

It is a required additional fixed-pi premise, never asserted here.

3. T64 row criterion: `t64/AggregateFejerCriterion.lean`, SHA
   `ce4dac5fbb5ab1e7dd539e8dcc81a2c58351d4078e8e30ca774e30fea612ab16`,
   lines 1715-1757 and 1843-1924, requires, for `q=10^ell` and a common
   prefix `P`, both

```text
B_successor + (1/2) B_parent <= P/(40q),
||rowFourierRemainder(ell,P)|| <= P^2/(10q).
```

4. T83 literal sparse-scale interface:
   `t83/T83LiteralStatisticAudit.lean`, SHA
   `013170204762b54fd9e8791f6723f189473ccbf03d4a4ec7b63ad657e44ea424`,
   lines 30-70 and 192-268, uses
   `L_n=10^floor(n/2)` and retains an effective-irrationality premise plus
   all-rates residual-long decay. Neither premise is established for pi.

## 6. Retained fingerprint cards

### 6.1 F1: Mahler log-periodic radial oscillation

FINGERPRINT_CARD: F1

SOURCE_CLAIM: S3, Poulet-Rivoal Theorem 2. Fix `r>=2` and rational power
series `a,b` satisfying H1-H6 on printed pp. 5-6:

```text
a,b have nonnegative coefficients; a(0)+b(0)=1;
a,b are defined at 1 and have no pole in the unit disk;
a,b are not both constant;
for every z in [0,1], |r*z^(r-1)*b(z)| < a(z^r)^2.
```

For the normalized positive holomorphic solution of

```text
y(z)=a(z)y(z^r)+b(z)y(z^(r^2)),
```

put `mu(z)=f(z)/f(z^r)`, define its Mellin transform `M`, let `mu1` be the
larger root of `X^2-a(1)X-b(1)`, and choose `alpha>1` by
`r^alpha*b(1)=a(1)^2`. The theorem says that `M` continues to the stated
half-plane with simple poles at 0 and -1 and, for every `epsilon>0`, as
`s -> 0+`,

```text
f(e^(-s)) = exp(log_r(mu1)*log(1/s) + c0
  + (1/log r) sum_(k!=0) M(2*pi*i*k/log r)*s^(-2*pi*i*k/log r)
  + c1*s + O_epsilon(s^(min(alpha,2)-epsilon))).
```

The source states absolute convergence and invariance of the Fourier term
under `s -> r*s`. This is a radial positive-real statement, not a unit-circle
or finite exponential-sum estimate.

NORMALIZED_FINGERPRINT: positive order-two Mahler recursion -> Mellin poles
-> explicit Fourier series periodic in `log_r(1/s)` -> coherent radial
amplitude.

NEAREST_BRANCH: T89's Kempner/Fredholm functional recurrence is the nearest
closed functional-equation model, while obstruction-memory cards T54/T56/T57
warn that exact multiplier-ten recurrence can leave a terminal phase rather
than cancellation. F1 differs by supplying a sourced asymptotic Fourier
amplitude, but it remains radial and does not evaluate a circle character.

REJECTION_TEST: set `s_m=r^(-m)`. For each integer `k!=0`,

```text
s_m^(-2*pi*i*k/log r) = exp(2*pi*i*k*m) = 1.
```

Hence the oscillatory factor is constant on this geometric subsequence, while
the leading term is `mu1^m`. Under H1-H6 collectively, the source derives
`mu1>1`; Theorem 2 therefore implies
coherent radial growth and the consecutive ratio tends to `mu1`; it supplies
no power saving for a signed length-`J` circle sum. This is an exact scaling
rejection, not finite evidence.

TRANSFER_PREMISE: transfer toward T10 would additionally require a theorem
that converts the radial Mellin coefficients into the exact unit-circle sum at
the prescribed point and proves, uniformly for every legal adaptive tuple
`(A,n,r,h,J)`, the displayed `F10(A,n,r,h,J)` bound. An identity with two
explicit errors each at most `J/(524288*A^2*n^2)` would suffice. S3 supplies
neither such an identity nor any estimate at the point pi.

DISPOSITION: close. The sourced periodicity is coherent growth, not the
missing adaptive cancellation mechanism.

### 6.2 F2: two-coordinate torus pairwise independence

FINGERPRINT_CARD: F2

SOURCE_CLAIM: S5 defines, for an increasing integer sequence `a=(a_n)`,

```text
W(psi,a,alpha) = {gamma in [0,1]:
                   ||a_n*alpha-gamma|| < psi(n) infinitely often}.
```

Theorem 2 states: for every increasing integer sequence `a` and every
`psi:N->R_nonnegative` with `sum_n psi(n)=infinity`, for Lebesgue-almost every
`alpha`, the set `W(psi,a,alpha)` has full Lebesgue measure. No monotonicity of
`psi` is assumed. Lemma 8 states that for distinct `m,n`, the two-dimensional
events

```text
A_n={(alpha,gamma): ||a_n*alpha-gamma||<psi(n)}
```

are pairwise independent under Lebesgue product measure. Its proof integrates
first in `gamma`, forcing opposite Fourier modes, and then in `alpha`, killing
the remaining mode because `a_m!=a_n`.

NORMALIZED_FINGERPRINT: lift prescribed times to the parameter-target torus
-> exact Fourier orthogonality in two coordinates -> pairwise independence for
arbitrary increasing times.

NEAREST_BRANCH: T87's metric-theorem kill endpoint and T88's artificial
measure boundary are nearest. F2 is semantically distinct from scalar
irrationality, rational order, semigroup density, and representation transfer
because the extra target coordinate creates exact pairwise independence. Its
strength is nevertheless averaged over the parameter coordinate.

REJECTION_TEST: for `0<rho<=1/4`, `a_j=10^j`, and

```text
B_j(alpha,rho)={gamma: ||a_j*alpha-gamma||<rho},
```

Lemma 8 gives exactly

```text
integral_alpha sum_(i,j<N) length(B_i intersect B_j)
  = 2*N*rho + 4*N*(N-1)*rho^2.
```

The diagonal terms have measure `2*rho`; distinct terms have product measure
`4*rho^2`. This exact average does not upper-bound the fiber at any specified
`alpha`. The quantifier mismatch survives even when `a_j=10^j`.

TRANSFER_PREMISE: a sufficient additional fixed-fiber premise toward the T7
finite near-return frontier would be the following unproved statement. Put
`rho_m=10^(-m)` and
`B_j={gamma: ||gamma-10^j*pi||<rho_m}`. There exists a fixed `C>=2` such that

```text
for every A>=1 there exists m0 such that for every m>=m0
there exists N>=2*C*A*m with
  C*rho_m <= 1/(2*A*m), and
  sum_(i,j<N) length(B_i intersect B_j)
    <= C*(N*rho_m + N^2*rho_m^2).                 (P_fiber)
```

This is not asserted for pi. Conditionally, if a pair is counted by
`Q_pi(m,N)`, its two radius-`rho_m` balls overlap in length greater than
`rho_m`. Thus `(P_fiber)` would give

```text
Q_pi(m,N) <= C*N + C*N^2*rho_m <= N^2/(A*m).
```

This proof sketch displays exactly what the source's parameter average lacks.

DISPOSITION: hold as model. The torus-lift orthogonality is semantically new,
but no fixed-fiber estimate is sourced.

### 6.3 F3: nonlinear derivative-cocycle Fourier decay

FINGERPRINT_CARD: F3

SOURCE_CLAIM: S8 defines total nonlinearity by requiring
`tau=log|T'|` not to have a representation

```text
tau = psi0 + g o T - g,
```

where `g` is `C^1` and `psi0` is constant on each branch. Theorem 1.1 says:
if `T` is a totally nonlinear uniformly expanding finite-branch Markov map of
bounded distortion and `mu` is a non-atomic equilibrium state for a potential
with exponentially vanishing variations, then its Fourier coefficients decay
at a polynomial rate in either of two cases: the branch intervals cover
`[0,1]` and inverse branches are `C^2`, or the intervals are disjoint and the
inverse branches are analytic.

NORMALIZED_FINGERPRINT: finite nonlinear expanding dynamics -> Dolgopyat
contraction for twisted transfer operators -> derivative nonconcentration and
sum-product -> polynomial Fourier decay of a deterministic Gibbs measure.

NEAREST_BRANCH: T88 is the nearest model-measure boundary. Unlike T63/T68 and
T78-T90, F3 obtains cancellation from a nonlinear derivative cocycle rather
than rational approximation, modular order, scalar packing, or explicit-point
construction.

REJECTION_TEST: for the decimal map `T(x)=10*x mod 1`,
`tau=log|T'|=log 10` is constant. Taking `psi0=log 10` and `g=0` gives the
forbidden cohomological representation exactly. Therefore the defining total
nonlinearity hypothesis fails before any decay exponent is considered. This
is an exact structural rejection, not a numerical experiment.

TRANSFER_PREMISE: transfer toward T64 would require a strictly increasing
common cutoff sequence `N(k)` and a quantitative representation of the actual
fixed-pi parent/successor row observables by a qualifying nonlinear Gibbs
system which, simultaneously for every required `ell<m<=k`, `q=10^ell`, and
`P=N(k)`, proves

```text
B_successor + (1/2) B_parent <= P/(40q),
||rowFourierRemainder(ell,P)|| <= P^2/(10q).
```

It must preserve all starts, half-open boundary counts, and the frequency
boxes in T64. S8 provides no conjugacy or approximation involving pi.

DISPOSITION: hold as model. This is the strongest deterministic cancellation
engine found, but its load-bearing hypothesis excludes the linear decimal map.

### 6.4 F4: ambient fractal Fourier decay for the exact geometric sum

FINGERPRINT_CARD: F4

SOURCE_CLAIM: S12 Theorem 1.2 states: if an IFS on `[0,1]` consists of
analytic contractions and at least one map is non-affine, then for every
self-conformal measure `mu` there exist `C,eta>0` such that

```text
|mu_hat(xi)| <= C*|xi|^(-eta) for every xi!=0.
```

Proposition 2.5 says any polynomial-Fourier-decaying measure has Properties
A-C. Property C quantifies over every integer `b>=2`, every
`psi:N->[0,1/2]`, every target `gamma`, and every `epsilon>0`, and gives for
`mu`-almost every `x`

```text
#{1<=j<=N: ||b^j*x-gamma||<=psi(j)}
 = 2*Sigma(N)
   + O(Sigma(N)^(1/2)*log(Sigma(N)+2)^(2+epsilon)).
```

Theorem 2.7 applies this to the IFSs of Theorem 1.2. The exceptional set and
implied constant may depend as stated by the source; no named fixed point is
placed in the full-measure set.

NORMALIZED_FINGERPRINT: nonlinear analytic self-conformal system ->
polynomial Fourier decay of an ambient parameter measure -> an `L^2` bound for
the exact geometric phase sum and metric shrinking-target laws.

NEAREST_BRANCH: T88's model-measure boundary and T90's named-point
discriminator are nearest. F4 is more directly aligned with T10 than generic
normality because Fourier decay can be inserted into the exact second moment,
but it remains a measure-average statement.

REJECTION_TEST: define

```text
S_(c,J)(x)=sum_(j=0)^(J-1) e(c*10^j*x),  c>=1.
```

The source decay gives the derived `proof sketch` bound

```text
integral |S_(c,J)|^2 dmu <= J + D_(C,eta),
D_(C,eta)=2*C*sum_(j>=1) j*(9*10^(j-1))^(-eta) < infinity.
```

Indeed `10^j-10^k >= 9*10^(j-1)` for `0<=k<j`. Chebyshev at the T10
half-budget threshold gives

```text
mu{|S_(c,J)| > J/(262144*A^2*n^2)}
 <= 262144^2*A^4*n^4*(J+D_(C,eta))/J^2.
```

Even after optimistically dropping `D_(C,eta)`, this particular Chebyshev
upper bound is below one only if

```text
J > 262144^2*A^4*n^4
  = 68719476736*A^4*n^4.
```

This is not a T10 scale obstruction: in the machine-checked T10 quantifiers,
`n` is fixed before the universal choice of `K`, so `K` can be chosen above
this threshold (and higher to absorb `D_(C,eta)`). Instead, the exact rejection
is the fixed-fiber test. The point measure at the prescribed point has
`|delta_pi_hat(xi)|=1` for every real `xi`, so it has no Fourier decay; and
membership of pi in the support of an ambient `mu` would not place it in the
source theorem's full-measure set. Thus the theorem plus Chebyshev can locate
some good model points at sufficiently large `J`, but not the specified point
or one point uniformly across every adaptive multiplier. This rejects the
displayed theorem application, not the possibility of another pointwise
theorem.

TRANSFER_PREMISE: transfer toward T10 requires a pointwise maximal theorem
placing pi in the good set and uniform over every adaptive
`c=h(10^r-1)`, `1<=h<=256*A*n`, with the explicit `F10` bound. Merely placing
pi in the support of `mu`, or proving genericity for another measure, would
not discharge this premise. S12 supplies no such named-point theorem.

DISPOSITION: hold as model. It gives the cleanest direct `L^2` mechanism for
the exact sum, but the fixed-point and adaptive-uniformity gaps remain.

## 7. Eight screened sources not retained

Each row states only the source claim at the cited locator and the reason its
normalized mechanism was not admitted as a fifth fingerprint.

| Source | Exact source claim inspected | Cheap discriminator and nearest closed branch | Disposition |
|---|---|---|---|
| S1 Rajchert | Theorem 3.13: under its non-rational first-order Mahler equation, convergence, and nonvanishing hypotheses, `mu(f(b))=1+limsup d_(k+1)/d_k` | ordinary irrationality exponent gives scalar denominator control, not pair multiplicity or `q=10^j(10^r-1)` uniformity; repeats T87 restricted-irrationality branch | close |
| S2 Adamczewski-Bell-Smertnig | Theorem 1.2: for a `k`-Mahler series over the algebraic closure, bounded coefficient height is equivalent to `k`-automaticity, and `O(log n)` height is equivalent to `k`-regularity | a periodic sequence is automatic yet can have a twisted sum of magnitude `L`; finite-state classification alone repeats the excluded automatic/paperfolding lane | close |
| S4 Sanford | Definition 1 and Theorem 3 turn positive Diophantine density into infinitely many scalar approximants; Theorem 4 gives density `1-delta` to the complement of a set with counting function `O(n^delta)` | the relevant family `{10^u(10^v-1)}` has only `O((log X)^2)` members up to `X`, so Theorem 4 controls its complement, the wrong polarity; nearest T87 scalar branch | close |
| S6 Wang-Li-Li | Theorem 1.1: when `eta=limsup a_(n+1)/a_n=1`, the exact and upper level sets for the uniform exponent have dimension `((1-vhat)/(1+vhat))^2` for `vhat in [0,1]` | at `vhat=0` the threshold gives no shrinking; for `vhat>0` the theorem describes an exceptional set without locating a named point; repeats scalar restricted-return branch | close |
| S7 Varju-Yu | Theorem 1.5 bounds a self-similar measure's Fourier transform by an exponential of an arithmetic digit-change sum; Corollary 1.8 and Theorem 1.10 give logarithmic decay under non-Liouville translation-ratio hypotheses | this is a fixed artificial self-similar measure; frequency-growing transfer to empirical pi measures would require accuracy far stronger than weak convergence; nearest T88 | close |
| S9 Algom-Rodriguez Hertz-Wang | Theorem 1.1 gives polynomial directional Fourier decay for analytic planar self-conformal measures when the IFS is not conjugate to self-similar and its attractor is not in an analytic curve | the natural circle embedding lies on an analytic curve and decimal inverse branches are self-similar; both structural gates fail | close |
| S10 Rudnick-Technau | Theorem 1.1 gives Poisson pair correlation for `(alpha*a(x))` for Lebesgue-almost every `alpha` when `a` is Hadamard-lacunary | no effective exceptional-set removal or adaptive-multiplier uniformity; repeats the metric calibration boundary | close |
| S11 Chaubey-Yesha | Theorem 1 gives, for every fixed order `k>=2`, Poisson `k`-level correlations for almost every dilation of a positive lacunary sequence; Proposition 2 supplies its near-relation count | higher metric correlations still do not locate pi or yield the explicit adaptive T10 bound; same fingerprint as S10 | close |

## 8. Cross-card comparison

| Card | New input | What is genuinely controlled | Exact failure at decimal fixed-point interface | Cheapest future discriminator |
|---|---|---|---|---|
| F1 | Mellin analysis of a positive Mahler recursion | radial log-periodic amplitude | radial coherence is not unit-circle cancellation | an explicit boundary identity with two `F10/2` error budgets |
| F2 | two-coordinate Fourier orthogonality | exact pairwise independence after averaging over parameter and target | no bound on the specified parameter fiber | prove or falsify `(P_fiber)` for a deterministic non-pi model before any pi proposal |
| F3 | total nonlinearity and twisted-transfer spectral gap | polynomial Fourier decay of a deterministic Gibbs measure | `log|T'|=log 10` is locally constant | any proposed conjugacy must first avoid the exact cohomology witness `psi0=log 10,g=0` |
| F4 | polynomial decay of an ambient fractal measure | direct `L^2` control of the exact geometric sum | `delta_pi` has unit Fourier magnitude, while ambient almost-everywhere control does not locate the named point | a pointwise adaptive maximal theorem with explicit constants |

Only F2's torus lift and F3's derivative cocycle are semantically new relative
to the rational/scalar/automatic inventory. F3 is structurally incompatible
with the decimal map. F2 remains a clean related-model explanation of why
adding a target coordinate creates independence, but the fixed-fiber premise
is essentially the missing deterministic input. F4 supplies a useful exact-sum
calibration but not a pointwise route. F1 is closed.

## 9. Scope firewall

The following statements are deliberately explicit:

1. No delivered source states a theorem about pi.
2. No delivered source establishes the canonical ordered,
   diagonal-inclusive strict near-return estimate.
3. No delivered source establishes C1 or C2.
4. The implications from `(P_fiber)` and `F10` are conditional proof sketches;
   their antecedents are not known for pi.
5. The `mu` in the fractal papers is a model measure, not an empirical limit
   measure for the decimal orbit of pi.
6. Almost-everywhere theorems do not place pi outside their exceptional sets.
7. The rejection tests reject only the displayed theorem applications. They
   are not impossibility theorems for all future mechanisms.

## 10. Portfolio endpoint

PORTFOLIO_VERDICT: hold as model

The sole terminal verdict is **hold as model**. Retain F2 as the cleanest
semantically new model of exact independence and retain F3/F4 only as
cancellation comparators. Do not open a successor: F2's cheapest transfer
premise `(P_fiber)` already asks for the fixed-fiber information the program
lacks, F3 fails exactly for the decimal map, and F4 needs a named-point
adaptive maximal theorem. F1 is closed.

There is no bounded successor selected (`SUCCESSOR_COUNT: 0`). This endpoint
makes no claim about pi, C1, or C2.
