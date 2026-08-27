# T190: bounded symbolic-and-entropy discovery scout

## Scope, statement, and status

This is a literature-note survey for G28.  It is not a proof of any statement
about pi.  The byte-exact `canonical_statement.txt` is the canonical question;
its SHA-256 is
`cbf56699b651aeb69301265763e38da44feb59c6fd955d2280887e8c06c6a2f8`.
The canonical normalization counts ordered pairs and includes the diagonal.

The present scout is independent of unfinished T189: no T189 artifact,
source, assertion, fingerprint, or comparison was read or used.  T189 is not
an input to the ledger or to any conclusion below.

Vocabulary: source transcription is `literature-checked` only in the narrow
sense that the three vendored primary PDFs and the named locators were checked.
The elementary Cauchy--Schwarz calculation is displayed below.  All transfer
conditions are `conjecture`s, and all candidate conclusions are related-model
screens.  Nothing here is progress on pi, A1, C1, or C2.

## Definitions and target scale

For an infinite word `x`, overlapping starts `0,...,N-1`, and `m>=1`, let
`c_x(w;m,N)` be the number of starts whose length-`m` word is `w`, reading
through `N+m-2` without wrapping.  Define the ordered diagonal-inclusive
energy

```text
E_x(m,N) = sum_w c_x(w;m,N)^2.
```

Thus `sum_w c_x(w;m,N)=N`.  The common screen depth is
`m_N=floor((1/4)*log_10(N))`; it is at least one only for `N>=10^4`.
The model benchmark that an equidistributed decimal coding would have to
approach is `E_x(m,N) about N^2*10^(-m)` (up to its diagonal term).  It is a
related-model benchmark, not an asserted property of pi.

## Through-T188 exclusion ledger

The ledger is deliberately an exclusion/comparison ledger, not a chain of
premises.  `accepted sketch` means a recorded note accepted at sketch level;
its mathematical deductions remain unverified.  `machine-checked` refers only
to the named formal interface.  T188 is recorded as `revise/pipeline`, hence
it provides no usable mathematical artifact.

| recorded item(s) | recorded status or level | normalized closed branch for this scout | treatment here |
|---|---|---|---|
| T63 | recorded audit | BBP/rational-tail phase applicability | excluded; no rational-tail repair is searched |
| T68 | recorded audit | factorial/modular representation | excluded; no factorial digit route is searched |
| T78 | recorded audit | Euler--Rabinowitz--Wagon representation | excluded; no pi representation is searched |
| T79 | accepted sketch | valuation/order collision formula | excluded; not a symbolic theorem tuple |
| T80 | recorded audit | post-representation inventory | excluded |
| T81 | recorded audit | representation comparison | excluded |
| T82 | recorded audit | representation negative synthesis | excluded |
| T85 | recorded audit | post-T85 pi-specific direction scout | excluded; this is related-model only |
| T164 | accepted sketch | return/recurrence descriptors lose multiplicity | nearest boundary for C2 |
| T166 | machine-checked interface | finite-word power-free packing | nearest boundary for C2 |
| T176 | accepted sketch | Mahler support, automatic correlation, structured sums | nearest boundary for C3 |
| T181 | accepted sketch | cross-domain negative scout | nearest boundary for C1/C3 |
| T183 | accepted sketch | overlapping-iid concentration | excluded; no random input is used |
| T184 | accepted sketch | d-bonacci every-window lower floor | nearest boundary for C2 |
| T185 | no accepted artifact in supplied library | unavailable recorded comparison | no premise or availability claim |
| T186 | accepted sketch | d-bonacci two-sided factor energy | nearest boundary for C2 |
| T187 | accepted sketch | fractional deletion obstruction for iid energy | excluded; no iid concentration route |
| T188 | revise, pipeline; no artifacts | no completed mechanism | explicitly no premise |

This lists every required item, including the range T78--T82 and T183--T187.
It also states the duplication boundary: C1 is the already-screened
constant-length substitution/Fourier-ray family, C2 is the linear-complexity
collision-floor family, and C3 is the automatic rational-phase family.  They
are retained only to close them with source-level cards, not as new routes.

## Search cap and primary source tuples

Exactly three dated primary theorem tuples were searched, one in each required
domain.  They, their URLs, hashes, exact PDF locators, and applicability data
are in `SOURCE_LEDGER.csv`.  The primary-source cap is ten.  There are exactly
three retained candidate fingerprints, all source-, theorem-, and
mechanism-distinct:

```text
source tuples searched = 3 <= 10
symbolic domains searched = 3
retained fingerprints = 3 <= 3
surviving candidates = 0
```

## C1: constant-length substitution spectral ray

**Domain.** Spectral/Fourier theory of explicit substitutions.

**Pinned theorem and applicability card.** Baake--Gahler--Grimm,
arXiv:1201.1423v1 (6 January 2012), Eq. (11), PDF p. 8, and Lemma 1,
PDF pp. 9--11, applies to fixed integers `k,l>=1` and every `z in Z`,
`0<=s<k+l`.  It defines the primitive constant-length substitution
`rho_(k,l)` and proves

```text
eta((k+l)z+s) = (alpha_s eta(z)+alpha_(k+l-s) eta(z+1))/(k+l),
eta((k+l)z)=eta(z),   eta(0)=1.
```

For the source-defined `(k,l)=(5,5)`, the paper gives
`eta(1)=(k+l-3)/(k+l+1)=7/11`.  Hence its named Fourier statistic, the
autocorrelation coefficient, satisfies `eta(10^r)=7/11` for every `r>=0`.
All parameters are source-admissible: fixed `k=l=5`, integral `z`, and
`0<=s<10`.

**Fingerprint and nearest closed branch.**
`constant_length_substitution -> exact_base10_autocorrelation_ray`.
Nearest closed branch: T115's generalized Thue--Morse/Riesz recursion.  That
note is unverified comparison evidence; the source statement above is checked
again from the vendored PDF and is not imported from T115.

**Related-model claim.** At the target depth `m_N`, the model has the named
base-ten spectral ray `eta(10^(m_N))=7/11`; it therefore models persistent,
not decaying, Fourier autocorrelation on that ray.

**Cheap rejection calculation.** Take `N=10^16`, so `m_N=4`.  The exact
source recurrence gives `|eta(10^4)|=7/11>1/4`.  Thus this model fails even
the deliberately weak proposed ray-decay screen `|eta(10^(m_N))|<=1/4`.
This rejects its claimed cancellation scale; it says nothing about pi.

**Necessary transfer hypothesis (conjecture).** There would have to be a
carry-safe coding of the decimal orbit of pi into a source-admissible
`rho_(5,5)` hull, plus an effective comparison transferring its finite
autocorrelation coefficients to every required lag exponential sum of T10.
The source supplies neither coding, pi membership, nor such a comparison.

**Candidate verdict: CLOSE.** The source mechanism demonstrates persistent
ray correlation rather than the required cancellation.

## C2: automatic factor-complexity collision floor

**Domain.** Quantitative factor complexity and collision energy.

**Pinned theorem and applicability card.** Goc--Schaeffer--Shallit,
arXiv:1206.5352v1 (23 June 2012), Theorem 2, PDF p. 3, holds for every
infinite word `x` and every `n>=1`: the number of contiguous blocks of novel
length-`n` occurrences is at most
`rho_x(n)-rho_x(n-1)+1`.  On PDF p. 4 the authors state for Thue--Morse that
`rho_t(n)-rho_t(n-1)<=4`; with `rho_t(1)=2`, elementary telescoping gives
`rho_t(m)<=4m-2` for `m>=1`.  The theorem's range is all infinite words and
positive lengths; the displayed Thue--Morse specialization is binary and has
no decimal or pi hypothesis.

**Fingerprint and nearest closed branch.**
`linear_factor_complexity -> Cauchy_collision_energy_floor`.
Nearest closed branch: T164/T166/T184/T186, which similarly isolate that
low complexity gives a collision floor or fails to give an upper-energy
mechanism.  These are comparison labels only, not premises here.

**Related-model claim.** Cauchy--Schwarz, applied to the `rho_t(m)` occupied
fibres, gives the ordered diagonal-inclusive bound

```text
E_t(m,N) >= N^2/rho_t(m) >= N^2/(4m-2)       (m>=1).
```

This is a direct related-model collision-energy claim with the required
overlapping-start and diagonal-inclusive normalization.

**Cheap rejection calculation.** At `N=10^16`, `m_N=4`, this gives
`E_t(4,N)>=N^2/14`.  The uniform-decimal benchmark at the same depth is
`N^2*10^(-4)=N^2/10000`; their ratio is at least `10000/14>714`.
So a linear-complexity automatic word cannot furnish the desired small-energy
model at this logarithmic scale.

**Necessary transfer hypothesis (conjecture).** To move toward T7, one would
need a decimal, carry-safe factor map from the pi orbit whose length-`m`
cylinder multiplicities are controlled by a source theorem with
`rho(m)` comparable to `10^m`, uniformly over the relevant prefixes.  This
source supplies only a binary automatic word and no such map or upper bound.

**Candidate verdict: CLOSE.** Its explicit output is a lower collision floor,
opposite in direction to a T7 energy upper bound.

## C3: automatic rational-phase exponential sums

**Domain.** Automata, transducers, and carry-sensitive symbolic dynamics.

**Pinned theorem and applicability card.** Drappeau--Mullner,
arXiv:1710.01091v1 (3 October 2017), Definition 1 and Theorem 1,
PDF pp. 2--3, applies to an automatic sequence from a fixed base-`k` DFAO,
a rational function `f=P/Q` of total degree at most `d>=1` well-defined modulo
`q>=1`, and any nonempty integer interval `I`.  With `q_1` as defined in the
theorem, it bounds

```text
sum_(n in I) a_n e_q(f(n))
 << |I|^(1+epsilon) (1/q_1 + q^2/(q_1 |I|^2))^c.
```

Here `c>0` depends at most on `d` and the fixed automaton.  The same PDF,
p. 3, Remark 1, explicitly says this bound is trivial for linear or constant
polynomials and gives a failure example for `f(X)=X`.  The carry property is
Definition 2, PDF p. 7; Proposition 1, PDF pp. 7--8, reduces an admissible
bounded weight to two-point correlation sums.  The theorem controls rational
periodic phases, not the unweighted geometric phase of T10.

**Fingerprint and nearest closed branch.**
`finite_DFAO + rational_nonlinear_phase + carry_reduction -> short_sum_bound`.
Nearest closed branch: T176's automatic/structured-sum screen and T162's
automatic rational-phase screen.  Their notes are not used as premises.

**Related-model claim.** The named Fourier statistic is
`F_I(a,f,q)=sum_(n in I) a_n e_q(f(n))`.  The source bounds this statistic
only for its DFAO/rational-phase parameters; it does not bound
`sum_(j<N) exp(2*pi*i*h*pi*10^j)`.

**Cheap rejection calculation.** Let `N=10^4`, hence `m_N=1`, set
`q=N`, `a_n=1`, `f(X)=X`, and `I={0,...,q/2-1}`.  The geometric sum has

```text
|F_I(1,X,q)| = 1/|sin(pi/q)| > q/pi.
```

This order-`q` calculation is exactly the obstruction identified in the
source's Remark 1: the theorem's useful saving is unavailable for a linear
phase.  In particular, one must not replace the theorem's `q_1` by `q` in this
example; its definition is part of the applicability conditions.  The T10
phase is not rational-polynomial in the index, so the source cannot be applied
by relabelling it.

**Necessary transfer hypothesis (conjecture).** Toward T10 or T64, one would
need an effective representation, uniform in every required `h` and prefix,
of the unweighted phase `exp(2*pi*i*h*pi*10^j)` as a source-admissible DFAO
coefficient times an admissible nonlinear rational periodic phase, with an
error below the corresponding Fourier and boundary budgets.  The source gives
no such representation, and no one is asserted.

**Candidate verdict: CLOSE.** The phase class and weight are incompatible
before any carry estimate can reach a pi frontier.

## Source-pinned negative map and endpoint

The three source-pinned cells close respectively because: C1 has an explicit
nondecaying base-ten spectral ray; C2 has an explicit logarithmic-depth
collision floor; C3 requires a rational nonlinear periodic phase while T10
has an unweighted geometric irrational phase.  This is a source-pinned
negative map for these three recycled symbolic directions, not an exclusion of
unsearched symbolic work.

**BATCH VERDICT (1/1): CLOSE.** There are zero survivors, so no successor is
selected.  No finite computation was used; the three displayed calculations
are algebraic applicability/rejection checks, not evidence for a universal
claim.

## Replay

From a directory containing only these delivered files, run:

```text
python3 verify_t190.py
sha256sum -c SHA256SUMS
```

The verifier checks the canonical hash, all three vendored source hashes,
all required ledger identifiers, the three distinct domains, the caps, exact
locator markers, three applicability/rejection/transfer/verdict cards, the
one batch verdict, the T189-independence declaration, and no-successor rule.
