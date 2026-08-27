# T163: bounded G28 cross-domain mechanism scout

Audit date: 2026-08-12 UTC.

Statements explicitly attributed to S1-S5 are `literature-checked` against the
pinned primary PDFs and exact locators in `SOURCE_PINS.md`. All substitutions,
comparisons, and transfer analyses newly made here are `proof sketch`.
`verify_t163.py` and `raw_output.txt` are a finite-test `experiment`: they check
artifact integrity, caps, ledger coverage, and displayed arithmetic, not any
universal theorem. Each named fixed-pi input is an `unproved pi transfer` and is
not asserted.

```text
PRIMARY_SOURCE_COUNT: 5
PRIMARY_SOURCE_CAP: 10
SEARCHED_DOMAIN_COUNT: 4
SEARCHED_DOMAIN_MINIMUM: 3
RETAINED_FINGERPRINT_COUNT: 3
RETAINED_FINGERPRINT_CAP: 3
EXCLUSION_LEDGER_RANGE: T89-T161
EXCLUSION_LEDGER_COUNT: 73
COMPARATOR_RESERVATION_COUNT: 2
SCOPED_VERDICT_COUNT: 1
SUCCESSOR_COUNT: 0
FIXED_PI_CLAIM: none
A1_CLAIM: none
C1_CLAIM: none
C2_CLAIM: none
```

## 1. Immutable statement, scope, and ambiguities

The canonical question has no original Erdos Problems URL. Its provenance says
that this program formulated it on 2026-07-22. The delivered byte-exact
`canonical_statement.txt` has SHA-256

```text
cbf56699b651aeb69301265763e38da44feb59c6fd955d2280887e8c06c6a2f8.
```

It asks whether, for the fixed orbit of pi, every integer `A>=1` has an `n0`
such that every `n>=n0` admits some `N>=1` with
`A*n*Q_pi(n,N)<=N^2`. The count is ordered, includes all diagonal pairs, uses
strict circle distance, and permits `N` to depend on `A,n`. T163 neither changes
nor answers this question.

This scout studies only A13/A14 related models. Ambiguities are fixed as follows.

1. A source is counted once when its primary PDF was retrieved and inspected,
   whether retained or screened.
2. The four searched domains are Mahler/functional equations,
   restricted-denominator approximation, arithmetic/fractal Fourier decay,
   and symbolic collision theory. No short-sum source is counted because the
   now-accepted T160 comparator already reserves the discovered tuple.
3. A fingerprint may use two sources only when the later theorem sharpens the
   same construction; S3-S4 form one fingerprint, not two candidates.
4. A related-model almost-everywhere, Hausdorff-dimension, Fourier-dimension,
   or two-independent-sequence result does not locate pi or control one finite
   pi prefix.
5. T159 and T161 are unverified notes. Their calculations are conditional
   comparator warnings, never discharged premises.
6. T160 and T162 are now accepted literature comparators in the refreshed
   snapshot. Their complete pinned source/theorem tuples are reserved and no
   deduction from either report is imported as a premise.

## 2. Bounded clean-context search and ledger

The search stopped after five previously unaudited primary PDFs across four
domains. `SOURCE_PINS.md` records exact versioned URLs, hashes, theorem/page
locators, and use. The retained fingerprints are:

```text
C-GCD    = (S2 SHA, Theorem 1, two inhomogeneous multiplicative phases,
            explicit gcd covering penalty)
C-SHELL  = (S3+S4 SHAs, Theorem 1.1 + Theorem 1.4.1/Lemma 4.3.2,
            denominator-shell incidence and exact lattice spectral gap)
C-XMATCH = (S5 SHA, Theorem 7, Renyi-2 longest cross-match threshold)
```

S1's exact tuple was unaudited, but its mechanism was rejected as a renamed
closed branch: Mahler functional-equation lifting converts continued-fraction
degree gaps into a scalar irrationality exponent. This remains nearest to T89's
scalar irrationality warning, T114's determinant/Hankel route, T127's Mahler
lifting, and T136's regular/Mahler screen. It supplies no adjacent compatibility,
prescribed-character cancellation, or collision multiplicity.

`EXCLUSION_LEDGER.csv` has exactly one row for every T89-T161 identifier. It
extends the accepted T158 ledger with T158-T161 and separately includes the
required T162 reservation. In the refreshed snapshot, T160 and T162 are both
accepted, source-pinned literature artifacts. T160 reserves all six source
tuples, especially Dębowski `1609.04683v4`, Kosolobov `2410.00209v1`,
Pirsic--Stockinger `1710.09313v2`, He--Liao `2302.05149v2`,
Fouvry--Kowalski--Michel `1307.0135v2`, and Fouvry--Kowalski--Michel--Raju--
Rivat--Soundararajan `1508.00512v3`. T162 reserves Dvorakova--Medkova--
Pelantova `2003.06916v3`, Klouda--Medkova--Pelantova--Starosta
`1801.09203v3`, and Drappeau--Mullner `1710.01091v1`, with the theorem
locators recorded in those artifacts' `SOURCE_PINS.md`. No T160/T162 proof-
sketch deduction is imported. Exact tuple absence from earlier readable files
is a bounded deduplication statement, not literary novelty.

## 3. Candidate C-GCD: simultaneous restricted-denominator covering

### 3.1 Literature-checked theorem

S2 begins with real sequences `a_n,b_n,c_n,d_n` satisfying
`1<=a_n<=b_n` for every `n in N`, then defines

```text
M(psi)={x in [0,1]: ||a_n*x+c_n||*||b_n*x+d_n||<psi(n)
                         for infinitely many n}.
```

Theorem 1 further restricts the `a_n,b_n` sequences to positive integers; the
shifts `c_n,d_n` remain real. For `0<s<1`, it gives
`H^s(M(psi))=0` if

```text
sum_n b_n*(psi(n)/b_n)^s
 + sum_n gcd(a_n,b_n)*(psi(n)/(a_n*b_n))^(s/2) < infinity.  (3.1)
```

It also gives a Lebesgue convergence criterion with the displayed logarithmic
and gcd terms in S2. This is a convergence/exceptional-set theorem over variable
`x`; it is not a bound for a named point.

### 3.2 Related-model deduction and quantitative test

Fix distinct positive integers `u,v`, put

```text
a_n=u*10^n,  b_n=v*10^n  (after ordering u<=v),
psi(n)=10^(-2*kappa*n),  kappa>0.                         (3.2)
```

For the first series in (3.1), the nth exponential factor is
`10^(n*(1-s*(1+2*kappa)))`, so it converges exactly when
`s>1/(1+2*kappa)`. Since
`gcd(a_n,b_n)=gcd(u,v)*10^n`, the second series has nth exponential factor
`10^(n*(1-s*(1+kappa)))`, and converges exactly when

```text
s>1/(1+kappa).                                             (3.3)
```

Thus the gcd term is decisive and S2 gives the related-model upper bound
`dim_H M(psi)<=1/(1+kappa)`. The finite replay checks these exponents at
`kappa=1`, where the thresholds are `1/3` and `1/2`.

**Applicability/falsification test C-GCD.** A proposed use must first produce
two T28-adjacent phases with the same index `n`, legal integer multipliers, and
shrinking product at rate `10^(-2*kappa*n)`. Even then, (3.3) only makes the
exceptional set have dimension below one. It does not show `pi` lies outside
that set and does not impose T28's exact cross-error inequality
`Q0*e1+U*Q1*e0<1`. Failure to produce that inequality falsifies the transfer,
not the source theorem.

### 3.3 Additional unproved transfer toward T28

`PI-GCD-T28` (`unproved pi transfer`): for every adjacent node required by the
T26/T28 resonance chain, select legal T24-shaped indices and integers with the
source's simultaneous shrinking-target estimate **and**, independently,

```text
Q0*e1 + U*Q1*e0 < 1,
```

together with T28's denominator cap and exponent-eight closing bounds. S2
contains none of this prescribed-point coherent selection. Assuming only that
pi avoids the S2 limsup would also be an unproved fixed-point premise, not a
consequence of its Hausdorff-null conclusion.

Nearest prior branch: T104's restricted-denominator candidate and T28's exact
adjacent compatibility interface. Distinction: the gcd penalty for two
inhomogeneous integer phases is a new related-model diagnostic; the missing
prescribed-point/coherent-selection premise is unchanged.

## 4. Candidate C-SHELL: denominator incidence creates Fourier decay

### 4.1 Literature-checked theorems

S3 works in dimension one with an infinite `Q subset Z`, a function
`Psi:Z->[0,infinity)` that is positive on `Q`, bounded, and normalized by
`Psi(0)=1`, and a shift `theta in R`. For `M>0`, it defines
`Q(M)={q in Q:M/2<|q|<=M}` and
`epsilon(M)=min_{q in Q(M)} Psi(q)`. Theorem 1.1 assumes a real `a>=0`, an
increasing function `h:(0,infinity)->(0,infinity)`, and an unbounded set
`calM subset (0,infinity)` such that

```text
Q(M)={q in Q:M/2<|q|<=M},  epsilon(M)=min_(q in Q(M)) Psi(q),
|Q(M)|*epsilon(M)^a*h(M) >= M^a for every M in calM.         (4.1)
```

It constructs a Borel probability measure supported on `E(Q,Psi,theta)` and,
for every real `xi` with `|xi|>e`, satisfies

```text
|mu_hat(xi)| << |xi|^(-a)*exp(log|xi|/loglog|xi|)*h(4|xi|). (4.2)
```

The construction's single-scale factor has the exact integer-frequency gap
`F_M_hat(ell)=0` for `0<|ell|<=M/2`; Lemma 9.1 gives its divisor-controlled
high-frequency bound.

S4 fixes integers `m,n>=1`, `Q subset Z^n`, `Psi:Z^n->[0,infinity)`, and
`theta in R^m`; the limsup set uses strict inequalities
`|xq-r-theta|<Psi(q)` for infinitely many `(r,q) in Z^m x Q`. It defines
`Psi_*(q)=Psi(q)/|q|` (max norm) and
`s(Q,Psi)=inf{s>=0:sum_{q in Q} Psi_*(q)^s<infinity}`. Theorem 1.4.1 says that
if
`sum_q Psi(q)^m<infinity`, then

```text
dim_F E(m,n,Q,Psi,theta)=min(2*s(Q,Psi),m*n).               (4.3)
```

For the lower-bound construction one fixes `s<s(Q,Psi)`, defines the unbounded
dyadic scale set `calM` and shell `Q(M)` in Section 4.1, then deletes every
`q` dividing a nonzero `ell in Z^(mn)` with
`|ell| <= (M/(2*log_2(M)^(n+1)))^(1/(2mn))` to obtain `Q'(M)`.
Lemma 4.3.2 assumes the bump construction of Section 4.2, including an integer
`K>0` with `K>mn+s`, and states: `F_M^(0)=1` for all `M>0`;
`|F_M^(ell)|<=1` for all `M>0, ell in Z^(mn)`; exact vanishing for
`M>=2` and `0<|ell| <= (M/(2*log_2(M)^(n+1)))^(1/(2mn))`; and, for every
`zeta>log 2`, the bound
`|F_M^(ell)| <= C_zeta |ell|^(-s) w_zeta(|ell|) log_2(M)^(n+1)` whenever
`M in calM`, `M>=M0`, and `ell in Z^(mn)` has `|ell|>=3`. These are
model-measure results; no claim here extends their ranges.

### 4.2 Related-model deduction and quantitative test

Specialize S4 to `m=n=1`. Take integers `h!=0` and `r>=1`, put the exact
T10-style coefficient `c=h*(10^r-1) != 0`, and define the denominator family

```text
Q_c={c*10^j:j>=0},       Psi_tau(q)=|q|^(-tau), tau>0,      (4.4)
```

with `Psi_tau(0)=1/2` and arbitrary nonnegative values off `Q_c`; only its
restriction to `Q_c` enters `E(1,1,Q_c,Psi_tau,theta)` and the sums below.

For every `s>0`,

```text
sum_(q in Q_c) (Psi_tau(q)/|q|)^s
 = |c|^(-(1+tau)*s)/(1-10^(-(1+tau)*s)) < infinity.        (4.5)
```

Hence `s(Q_c,Psi_tau)=0`, and S4 gives Fourier dimension zero. The same
obstruction appears in S3: a dyadic shell contains at most one element of
`Q_c`. On any unbounded scale set where such shells are nonempty, (4.1) with
`a>0` forces `h(M) >= C(c,a,tau)*M^(a*(1+tau))` for a fixed positive constant
`C(c,a,tau)`, cancelling the intended power in (4.2); empty shells cannot
satisfy (4.1).

**Applicability/falsification test C-SHELL.** Equation (4.5) is an exact
quantitative rejection of the direct T10 denominator substitution. A positive
decay exponent requires many denominators per shell, while T10's fixed
geometric ray has at most one. Enlarging `Q` restores an ambient model measure
but loses the prescribed T10 ray and the named point.

### 4.3 Additional unproved transfer toward T10

`PI-SHELL-T10` (`unproved pi transfer`): construct a denominator set with enough
shell density for some explicit `a>0`, prove that its S3/S4 measure controls the
exact prescribed coefficients `h*(10^r-1)*10^j`, and prove a pointwise maximal
bound at `x=pi` strong enough for T10's weighted Fourier budget. Membership of
pi in the limsup support, ambient `mu`-almost-everywhere cancellation, and the
pointwise maximal inequality are all absent from S3-S4. Replacing them by the
T10 conclusion itself would merely assume an accepted frontier.

Nearest prior branch: T104 F4 ambient fractal Fourier decay and T121 global L2.
Distinct mechanism: exact lattice orthogonality and divisor incidence build the
decaying measure from arithmetic denominator shells. The same named-point
barrier persists, and the literal decimal ray fails before that barrier.

## 5. Candidate C-XMATCH: Renyi-2 cross-match threshold

### 5.1 Literature-checked theorem

For a shift-invariant probability `P` on a finite-alphabet one-sided shift, S5
defines the longest common substring between two independent sequences,

```text
M_n(x,y)=max{m:x_(i+k)=y_(j+k), 1<=k<=m,
                   for some 1<=i,j<=n-m},
```

and lower/upper Renyi-2 entropy from `sum_C P(C)^2`. Theorem 7 says that positive
lower Renyi entropy gives the almost-sure upper bound
`limsup M_n/log n <= 2/lowerH2`. Exponential alpha-mixing or polynomial
psi-mixing gives the matching lower bound; under that mixing alternative, if
`H2` also exists, almost surely

```text
M_n(x,y)/log n -> 2/H2.                                   (5.1)
```

This concerns two independent sequences and their extreme match, not the
ordered self-collision energy of one sequence.

### 5.2 Related-model deduction and quantitative test

For independent iid uniform decimal sequences, every length-`m` cylinder has
mass `10^-m`, so `H2=log 10`. Thus (5.1) becomes

```text
M_n/log_10(n) -> 2.                                       (5.2)
```

For every fixed `epsilon>0`, cross-matches eventually disappear above
`(2+epsilon)log_10 n` and occur below `(2-epsilon)log_10 n`. The finite replay
checks the entropy identity and the two thresholds for `n=10^6, epsilon=0.1`:
`floor(1.9*6)=11` and `ceil(2.1*6)=13`.

**Applicability/falsification test C-XMATCH.** Any related random-model claim
predicting no collisions already at depth `o(log n)` contradicts (5.2). But
even zero cross-collisions between two independent tracks gives no upper bound
for repeated blocks within either track; a constant first track and a disjoint
second track is the finite separator. Therefore the source object cannot be
substituted directly for T7's ordered diagonal-inclusive self-energy.

### 5.3 Additional unproved transfer toward T7

`PI-XMATCH-T7` (`unproved pi transfer`): prove a self-joining theorem for the
single pi digit path whose off-diagonal joinings have a uniform Renyi-2
collision bound, then sum multiplicities to obtain, with T7's exact
quantifiers, some `N=N(A,n)` satisfying

```text
A*n*piCylinderCollisionEnergy(n,N) <= N^2.
```

An independent-copy extreme-value theorem does not provide this joining or
energy estimate. Assuming the displayed energy bound is exactly the T7
frontier, so it cannot be presented as a deduction from S5.

Nearest prior branch: T135 Renyi-2 projection tensorization and T150's symbolic
entropy/collision screen. Distinction: S5 sources the precise two-track extreme
threshold; it does not repair the self-energy or prescribed-path gap.

## 6. Universal separators and classification

The following are `proof sketch` or finite-test diagnostics, not source claims.

1. **Named-point separator:** a Hausdorff-null exceptional set may contain any
   specified point. C-GCD therefore cannot classify pi.
2. **Sparse-shell separator:** the exact geometric family in (4.4) has at most
   one denominator per dyadic shell and `s=0`. C-SHELL cannot produce positive
   Fourier decay on that literal family.
3. **Independent/self separator:** two sequences can have no cross-match while
   one has maximal self-collision energy. C-XMATCH controls the wrong joining.
4. **Frontier-equivalence separator:** adding T28's cross-error inequality,
   T10's prescribed pointwise sum bound, or T7's self-energy bound as an
   assumption does not constitute transfer; each is an accepted frontier or a
   load-bearing part of one.
5. **Comparator-duplication separator:** Dębowski and
   Fouvry--Kowalski--Michel were not retained because accepted T160 pins their
   exact PDFs and theorem tuples. All accepted T162 source/theorem tuples are
   likewise reserved; none duplicates C-GCD, C-SHELL, or C-XMATCH.

The three candidates are genuinely different source/mechanism tuples, but all
fail their cheapest direct transfer discriminator. C-GCD is a useful
two-resonance exceptional-set model; C-SHELL is an arithmetic construction with
an exact sparsity obstruction; C-XMATCH calibrates the wrong collision object.
No finite-pi experiment was run or used.

## 7. Replay and endpoint

From a directory containing only the delivered artifacts, run

```bash
python3 verify_t163.py > replay.txt
diff -u raw_output.txt replay.txt
sha256sum -c SHA256SUMS
```

The verifier checks the canonical hash, five PDF hashes, and four extract
hashes; source,
candidate, and domain caps; all T89-T161 rows and both comparator reservations;
distinct candidate keys; exact geometric-series convergence exponents;
Fourier-dimension-zero substitution; iid decimal Renyi entropy and finite
thresholds; label, claim, verdict, and successor markers. This replay is an
`experiment`, not evidence for a universal mathematical claim.

SCOPED_VERDICT (1/1): **hold as model**.

Hold only C-GCD's explicit gcd-penalized two-phase exceptional-set theorem and
C-SHELL's deleted-divisor spectral-gap construction as related-model diagnostic
tools. The literal decimal substitutions fail quantitatively, and neither
locates pi. C-XMATCH is retained in the exclusion map but closed as a transfer
route because independent extreme matches do not control self-collision energy.
This verdict makes no claim about fixed pi, A1, C1, C2, T7, T10, T28, or T107.

No successor is proposed.
