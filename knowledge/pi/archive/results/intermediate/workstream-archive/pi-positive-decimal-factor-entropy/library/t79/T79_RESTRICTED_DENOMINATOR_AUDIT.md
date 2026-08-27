# T79: restricted-denominator approximation audit for pi

Status: `literature-checked` for the bounded, source-pinned corpus in
`SOURCE_MANIFEST.md`; `machine-checked` only for the named declarations in the
vendored T56, T58, and T61 Lean files. The T60 note is a `proof sketch`, not a
discharged premise. Final bounded-corpus verdict: **NO AUDITED RESULT APPLIES**.

This is a negative applicability audit, not a proof that no useful theorem
exists in the literature. It makes no unconditional claim about C7, C2, C1,
or positive decimal factor entropy for pi.

## 1. Provenance, normalized statement, and ambiguities

The canonical problem was formulated locally and has no original external
source URL. Its byte-exact vendored statement has SHA-256

```text
a70dd741b27595aeb3dfc902b5e201579fed6bae24e2191f58c5ac64a22939e6
```

It asks whether there are fixed `eta > 0` and `N >= 1` such that
`p_pi(n) >= 10^(eta*n)` for every integer `n >= N`. T79 does not answer that
question. It audits one possible arithmetic input to the conditional T56-T61
chain.

The following readings are fixed throughout this audit.

1. `n/2` and `10^n/2` use natural-number division.
2. "Uniform eventual" means one constant and one cutoff work for every
   sufficiently large `n`, not for a subsequence and not with constants
   depending on `n`, `h`, `j`, or `r`.
3. An `APPLIES` verdict would require a theorem-level implication to either the
   complete exceptional-set statement `SI_pi` below or T61's complete signed
   premise. A theorem that matches only the denominator shape is not marked
   `APPLIES`.
4. "Complete search" means every theorem-level candidate retained from the
   dated, bounded query log in Section 8 appears in the matrix. It does not mean
   an assertion about all mathematical literature.
5. The strict Vaaler neighborhood is `< 1/(2H_n)`. A source using `<=` is not
   silently changed to `<`.
6. The arithmetic residual mask is retained. Removing it would change the
   statement, although an estimate over an unmasked superset could imply the
   masked nonnegative incidence bound. It cannot in general be inserted into a
   signed sum.

## 2. Machine-checked target and sketch-level frontier

For `n >= 1`, put

```text
L_n := 10^(floor(n/2)),
H_n := 10^n/2,
q_(j,r) := 10^j*(10^r-1).
```

The following range facts are `machine-checked` in the vendored files.

- T56, `mem_sparse_short_sector_iff`, lines 68-72: the short lags are exactly
  `0 < r`, `r < n`, and `r < L_n`.
- T58, `mem_shortRectangle_iff`, lines 53-66: the starts are exactly
  `0 <= j < L_n-r`.
- T58, `mem_positiveFejerFrequencies_iff`, lines 48-51: the positive
  frequencies are exactly `1 <= h < H_n`.
- T61, `mem_residualShortRectangle_iff`, lines 1759-1768: all those endpoints
  and `not ArithmeticExcluded(mu,c,Q0,n,j,r)` occur together.
- T61, `decimalCutoff_eq_centralRadius`, lines 2022-2029:
  `10^(-n)=1/(2H_n)` for `n>=1`.
- T61, `strictCentralIndicator_endpoint_pos` and `_neg`, lines 1837-1870:
  both equality endpoints have indicator zero.
- T61, `vaalerAnalyticCertificate_proved`, lines 1872-1892: the majorization,
  strict endpoints, and complete coefficient-sign classification are proved.
- T61, `signedStructuredDenominatorPremise_iff_quantifiers`, lines 2079-2094:
  one `B>0` and one `N>=1` must work for every `n>=N`.

The T60 note is explicitly a `proof sketch`. Its structured exceptional-set
form is used here only as the specification to be compared, not as a proved
new theorem:

```text
(SI_pi)  exists C>0, exists N>=1, for every n>=N,

  2*|{(r,j): 0<r<n, r<L_n, 0<=j<L_n-r,
        not ArithmeticExcluded(mu,c,Q0,n,j,r),
        exists p in Z,
          |pi-p/q_(j,r)| < 10^(-n)/q_(j,r)}|
    <= C*L_n.
```

Multiplication by the positive `q_(j,r)` identifies the strict rational
approximation event with `||q_(j,r)*pi|| < 10^(-n)`. This elementary
equivalence is also exactly the near-return event unfolded in T61 lines
2041-2066.

T61's sole fixed-pi premise is stronger and genuinely signed. In the notation
of T61 lines 1896-1913 it is

```text
exists B>0, exists N>=1, for every n>=N,

  2/H_n * |X_n|
    + 2*sum_(1<=h<H_n) c_H_n(h)
        * sum_((r,j) in X_n) cos(2*pi*h*q_(j,r)*pi)
  <= B*L_n,
```

where `X_n` is the complete masked rectangle and

```text
c_H(h) = 1/H * [sin(pi*h/H)/pi
                 + 2*(1-h/H)*cos(pi*h/H)].
```

T61 lines 1724-1737 and 1872-1892 prove that there is one transition ratio
`u in (1/2,1)`: `c_H(h)` is positive below `u`, zero on it, and negative above
it. Therefore an absolute-value estimate, a pointwise nonvanishing result, or
an existential density theorem is not a constant-preserving reduction to the
displayed signed premise.

## 3. Hypothesis keys for the complete matrix

Every retained candidate is tested against the same keys.

| Key | Exact requirement |
|---|---|
| `P` | The named target is the fixed number pi, unconditionally. |
| `D` | Denominators are exactly `q_(j,r)=10^j(10^r-1)`. |
| `R` | The complete ranges `0<r<n`, `r<L_n`, and `0<=j<L_n-r` are covered. |
| `V` | The strict neighborhood has radius `1/(2H_n)=10^(-n)`. |
| `F` | All frequencies `1<=h<H_n` are controlled simultaneously. |
| `U` | One constant and one cutoff work for every sufficiently large `n`. |
| `A` | The masked exceptional count is `O(L_n)` or a stronger aggregate bound. |
| `S` | The actual signed Vaaler coefficients, including both signs, are retained. |

`YES` means the source theorem has the exact feature. `PARTIAL` means a
specialization matches only part of it. `NO` names a failed hypothesis.

## 4. Complete theorem matrix

| ID | Source result | P | D | R | V | F | U | A | S | Verdict and first fatal obstruction |
|---|---|---|---|---|---|---|---|---|---|---|
| `IY-E` | Iyer, elementary construction, p. 4 | YES | YES | NO | NO | NO | YES | NO | NO | **DOES NOT APPLY:** exact block-repunit witnesses are existential and give only `1/(t+1)` scale; the produced lag need not satisfy `r<n`. |
| `IY-1` | Iyer, Theorem 1.1, p. 3 | YES | NO | NO | PARTIAL | NO | YES | NO | NO | **DOES NOT APPLY:** the logarithmic-square scale is obtained for arbitrary base-10 `0/1` digit denominators, not one consecutive repunit block. |
| `AB-5` | Adamczewski-Bugeaud, Theorem 5 and Lemma 1 | PARTIAL | YES | NO | PARTIAL | NO | NO | NO | NO | **DOES NOT APPLY:** denominators arise only from already-present repeated prefixes, and the conclusion permits transcendental pi. |
| `PVZZ-1` | Pollington et al., Theorem 1 | NO | YES for each fixed `r` | NO | PARTIAL | NO | NO | PARTIAL | NO | **DOES NOT APPLY:** the count holds for measure-almost every target, not fixed pi, and no cutoff is uniform in growing `r`. |
| `PVZZ-3` | Pollington et al., Theorem 3 | NO | NO jointly in `r` | NO | PARTIAL | NO | NO | PARTIAL | NO | **DOES NOT APPLY:** one fixed finite prime set cannot contain the prime divisors of `10^r-1` for all `r`, and the target is still almost every `x`. |
| `BLMV-8` | Bourgain et al., Theorem 1.8 | PARTIAL | NO | NO | NO | NO | YES for its own density statement | NO | NO | **DOES NOT APPLY:** it produces some `2^s5^t` multiplier at only polylogarithmic density radius, not the prescribed repunit differences or an upper count. |
| `CZ-M` | Corvaja-Zannier, Main Theorem (1.1) | NO | PARTIAL | NO | NO | NO | YES for its own finite-exception statement | NO | NO | **DOES NOT APPLY:** its multiplier `delta` must be algebraic, so `delta=pi` violates an explicit hypothesis. |
| `HA-C` | Hata, Lemma 2.2 and equations in Section 3 | YES | NO | NO | NO | NO | NO | NO | NO | **DOES NOT APPLY:** the construction supplies Gaussian-integer linear forms, not rational approximants proved to have denominator `10^j(10^r-1)`. |
| `BBP-1` | Bailey-Borwein-Plouffe, Theorem 1, (1.2) | YES | NO | NO | NO | NO | NO | NO | NO | **DOES NOT APPLY:** the source proves an identity and digit algorithm, not a theorem placing reduced truncation denominators in the target family. |

There are no `APPLIES` rows. Consequently there is no claimed positive
reduction to `SI_pi` or T61. The closest partial denominator match, `IY-E`, is
reduced with constants in the next section so that its failure can be checked
without relying on the matrix labels.

## 5. Constant-preserving audit of the closest matches

### 5.1 Iyer's exact block-repunit pigeonhole construction

Iyer defines

```text
t(b,N) = floor(log_b(N*(b-1)+1)-1)
S_d = 1+b+...+b^d,  0<=d<=t(b,N).
```

The argument on p. 4 gives, for every real `gamma`, either one `S_d` or a
difference `S_d-S_c`, each at most `N`, whose product with `gamma` has
nearest-integer distance at most `1/(t(b,N)+1)`. Set `b=10` and
`gamma=9*pi`. Without changing the approximation constant,

```text
q = 9*S_d       = 10^(d+1)-1
```

or

```text
q = 9*(S_d-S_c) = 10^(c+1)*(10^(d-c)-1).
```

Thus `q=q_(j,r)` exactly, with `j=0,r=d+1` in the first case and
`j=c+1,r=d-c` in the second, and

```text
q <= 9N,
||q*pi|| <= 1/(t(10,N)+1).                 (5.1)
```

The factor 9 in the height is explicit: an Iyer height `N` corresponds to a
T79 denominator height at most `Q=9N`. No approximation constant was lost.
The reduction nevertheless fails T79 in four exact places.

1. It produces one pair `(j,r)`, whereas `SI_pi` is an upper bound for all
   incidences in the complete rectangle.
2. If `t(10,N)<=n-2` is imposed to ensure every possible produced lag is
   `<n`, then (5.1) is no better than order `1/n`, not `10^(-n)`.
3. Every legal T79 denominator satisfies
   `q_(j,r)<10^(j+r)<=10^(L_n-1)`. If `9N` is taken at this height, then
   `t(10,N)=Theta(L_n)`, so (5.1) is only `Theta(1/L_n)`, i.e. of order
   `10^(-floor(n/2))`; moreover the produced lag may be `Theta(L_n)`, far
   exceeding `n`.
4. The source conclusion is `<=`, while the T61 indicator uses `<`.

Iyer's Theorem 1.1 improves the right side to `C_10/(log N)^2`, which has the
right exponential order when `log N` is of order `L_n`. But its witness is an
arbitrary integer whose base-10 digits are zero or one. Lemma 3.3 works on the
union of those integers and differences `10^d-10^c`; it does not force the
witness into the difference component. Lemma 3.4 transfers the union estimate
back to arbitrary `0/1` digit denominators, not to block repunits. Hence the
improved exponent and exact denominator shape never occur in the same source
conclusion.

Neither result has an `h`-uniform exponential-sum conclusion or sees the sign
of `c_H(h)`.

### 5.2 Exact eventually periodic denominator

Adamczewski-Bugeaud set `r_n=|U_n|` and `s_n=|V_n|`. Their Lemma 1 gives

```text
alpha_n = P_n(beta)/(beta^r_n*(beta^s_n-1)).             (5.2)
```

At `beta=10`, (5.2) has exactly the T79 denominator form, before optional
fraction reduction. Their equation (2) identifies the error tail after the
repeated prefix `U_n V_n^w`.

For decimal digits, both the original and periodic-completion digits lie in
`{0,...,9}`. With
`K=r_n+ceil(w*s_n)+1`, equation (2) therefore gives the explicit bound

```text
|alpha-alpha_n|
  <= 9*sum_(k>=K) 10^(-k)
  = 10^(-(r_n+ceil(w*s_n))).                (5.3)
```

Thus no hidden constant is needed. Relative to
`q=10^r*(10^s-1)`, the T79 window is approximately
`10^(-(n+r+s))`; the upper bound (5.3) could certify entry into that window
only when the selected repetition has enough excess, roughly
`(w-1)*s>=n`. A smaller actual error could arise from further matching digits,
so no converse is asserted. The source neither asserts that inequality for pi
nor supplies such a repetition for every legal `(r,s)`.

This is not a uniform approximation theorem for pi. The pairs `(r_n,s_n)`
exist only when the target's digit word already contains the prescribed
repetition. Theorem 5 concludes that `alpha` belongs to `Q(beta)` or is
transcendental. For `alpha=pi`, the second alternative is already true and
excludes no repetition. There is no count over all pairs, no common eventual
constant at T79's scale, and no all-frequency signed estimate.

### 5.3 Metric counts for fixed lags and smooth denominators

For one fixed positive `r`, the sequence

```text
q_j = (10^r-1)*10^j
```

is lacunary with ratio 10, so it fits Pollington et al. Theorem 1. That theorem
counts `||q_j*x-gamma|| <= psi(q_j)` with a main term and an error for
`mu`-almost every `x`. More explicitly, for Lebesgue measure, `gamma=0`, and
the constant choice `psi(q_j)=10^(-n)`, its displayed formula gives

```text
Psi(J)=J*10^(-n),
R(x,J)=2*J*10^(-n)
  + O((J*10^(-n))^(2/3)*log^(2+epsilon)(J*10^(-n)+2)).   (5.4)
```

Formula (5.4) is for each fixed `r`, fixed function `psi`, and almost every
`x`; its exceptional set, implicit constant, and eventual threshold are not
stated uniformly as `r` and the tied scale `n` grow. It does not identify
`x=pi`. Taking a countable intersection over fixed `r` neither proves pi is in
that conull set nor supplies one threshold for all `r<n`.

Theorem 3 permits sequences supported on a fixed set `S` of `k` primes and
replaces the exponent `2/3` in (5.4) by `1/2`. It covers `{2^a5^b}` with
`S={2,5}`, but no finite `S` contains the prime divisors of every `10^r-1`:
for every prime `ell` other than 2 and 5, Fermat's theorem gives
`ell | 10^(ell-1)-1`. Both the fixed-target and complete-range quantifiers
therefore fail before one reaches T61's coefficient signs.

## 6. Exact obstructions for the remaining sources

### 6.1 Multiplicative semigroup orbit density

Bourgain-Lindenstrauss-Michel-Venkatesh Theorem 1.8 assumes a fixed irrational
`alpha` with `|alpha-p/q|>=q^(-k)` and proves that
`{a^s*b^t*alpha:s,t<=N}` is `(log log N)^(-kappa_6)`-dense for
multiplicatively independent `a,b`.

Even granting the separate ordinary irrationality input needed to instantiate
this at `alpha=pi`, `a=2`, and `b=5`, the theorem has the wrong conclusion.
At `N=L_n`, its radius is only a negative power of `log log L_n`, hence a
negative power of `log n`, not `10^(-n)`. It chooses some semigroup multiplier,
not every `10^j(10^r-1)`, and density gives neither an upper incidence count nor
a signed cosine sum. This audit does not reuse the ordinary irrationality
measure as a T79 result.

### 6.2 Algebraic S-unit approximation

Corvaja-Zannier's Main Theorem fixes a finitely generated multiplicative group
`Gamma` of algebraic numbers, a nonzero algebraic `delta`, and `epsilon>0`.
For each `u`, put `d=[Q(u):Q]`. Apart from pseudo-Pisot exceptions, only
finitely many `(q,u)` satisfy

```text
|delta*q*u| > 1,
0 < ||delta*q*u|| < H(u)^(-epsilon)*q^(-d-epsilon).
```

The substitution `delta=pi` is forbidden because pi is transcendental. If one
instead puts the decimal power into `u` and the repunit and frequency into the
integer `q`, the same algebraicity failure remains. In addition, the result is
pointwise and has no aggregate or coefficient-sign conclusion.

### 6.3 Pade and polylogarithmic constructions

Hata's Lemma 2.2 constructs a clearing integer

```text
D_n = Delta_1(n)*Delta_2(n)/Delta_3(n),
```

where the displayed products run over primes. Section 3 then forms simultaneous
linear forms `q_n*pi-p_n` and `q_n*log(2)-r_n`, with
`p_n,q_n,r_n` in the Gaussian integers and `q_n=D_n*v_n`. The source does not
turn this coefficient into a sequence of reduced positive rational
denominators, much less prove that those denominators equal
`10^j(10^r-1)`. The prime factors of `D_n` alone would not rule out cancellation,
so no such inference is made here. Hata's final all-denominator irrationality
measure is ordinary irrationality-measure ground and is intentionally not
reused; T60 already audited that route.

The BBP identity is

```text
pi = sum_(k>=0) 16^(-k)
       * (4/(8k+1)-2/(8k+4)-1/(8k+5)-1/(8k+6)).
```

The `k=0` truncation is exactly `47/15`, which is not of the target form. Before
fraction reduction, longer truncations involve the varying linear factors
`8k+d`, but cancellation could occur; this audit does not claim universal
nonmembership of every reduced truncation denominator. The exact source-level
obstruction is that BBP proves the identity and a hexadecimal digit-extraction
algorithm, not any theorem placing reduced truncation denominators in the T79
family. It gives no T79 count and no T61 signed estimate.

## 7. Verdict

**NO RETAINED THEOREM APPLIES TO `SI_pi` OR T61.**

The exact-denominator literature found in this bounded audit is existential,
conditional on repetitions, or almost-everywhere. The strongest
logarithmic-square estimate loses the block-repunit denominator. Results for
powers of 2 and 5 either require an algebraic target, quantify over almost
every target, or provide only orbit density. The Pade and BBP constructions
do not prove that their linear-form coefficients or reduced truncation
denominators belong to the T79 family. None retains simultaneously:

```text
fixed pi;
every sufficiently large n;
0<r<n and r<L_n;
0<=j<L_n-r;
1<=h<H_n;
the strict radius 1/(2H_n);
the arithmetic mask;
an O(L_n) aggregate;
the actual sign-changing Vaaler coefficients.
```

This establishes only that the exact restricted-denominator frontier is absent
from the audited, source-pinned corpus. It does not establish a logical
nonimplication from every possible restricted-denominator theorem, and it does
not construct any premise needed for the conditional T61-to-C7 chain.

## 8. Dated bounded search log

Search date: 2026-08-03 UTC. Databases and full-text endpoints used were arXiv,
Crossref/DOI metadata, OpenAlex, publisher repositories, Project Euclid/IMPAN
mirrors, and NASA NTRS. The bounded search stopped after the following query
families and primary-source inspection of the nine matrix rows.

| Query family | Result retained or disposition |
|---|---|
| `"rational approximation" "digit-restricted denominators"` | Iyer, exact arbitrary `0/1` denominators and elementary block differences. |
| `repunit Diophantine approximation denominator` | No theorem-level repunit/pi hit; Iyer and periodic-completion literature were the structural matches. |
| `"10^n-1" pi approximation` | No relevant theorem-level indexed hit. |
| `eventually periodic denominator integer base approximation` | Adamczewski-Bugeaud Theorem 5 and Lemma 1. |
| `restricted denominators finite prime set` | Pollington et al. Theorems 1 and 3. |
| `powers of 2 powers of 5 Diophantine approximation` | Bourgain et al. Theorem 1.8; no fixed-pi T79 count. |
| `S-unit rational approximation multiplicative group` | Corvaja-Zannier Main Theorem; algebraic-target obstruction. |
| `Pade rational approximations pi denominator` | Hata construction; ordinary final irrationality measure excluded. |
| `base 16 pi linear form digit extraction` | BBP identity; no theorem placing reduced truncation denominators in the T79 family. |
| `fixed pi discrepancy lacunary sequence` | Metric almost-everywhere results only; no fixed-pi theorem retained. |

Ridout-type algebraic-target results and additional ordinary irrationality
measures were triaged but not retained because their decisive obstructions are
already represented by `CZ-M` or the route is explicitly excluded by T79.
Recent conditional/preprint results about abstract denominator sets were not
used because they do not establish their hypotheses for the T79 family.

## 9. Replay

From a directory containing only these delivered artifacts, run:

```sh
sh ./verify.sh
```

The script checks every retained byte hash, extracts each PDF with
`pdftotext -layout`, checks theorem-level anchors, and checks the exact T56,
T58, T60, and T61 locators used above. Extracted text is a locator aid; the
pinned PDFs are authoritative.
