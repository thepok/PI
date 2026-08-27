# T35: theorem-by-theorem novelty audit

Status: `literature-checked` on 2026-08-01 for the bounded searches and
source pins below. The local Lean declarations identified as `machine-checked`
were previously accepted through the Lean gate; this literature audit does not
re-run or strengthen that verification. T30 remains only a `proof sketch`.

## 1. Immutable source and scope

The byte-for-byte vendored source is `pi-digits.txt`, SHA-256
`2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825`.
Canonical V1 asks whether every finite decimal word, including words with
leading zeroes, occurs contiguously in pi. Sibling V3 asks whether every
infinite decimal stream embeds as a scattered subsequence; equivalently, every
decimal digit occurs arbitrarily late. V1 and V3 are open and are not
interchanged in this audit.

The audit concerns only the principal implications in T20, T26-T30, T32, and
T33. A verdict describes the mathematical implication, not its Lean proof:

- `standard specialization`: a cited general statement specializes directly;
- `known consequence`: the implication follows by a short displayed reduction
  from cited statements;
- `Lean-only novelty`: reserved for mathematical content known elsewhere but a
  first formalization established by a sufficiently broad formal-library search;
- `no match found in the bounded search`: no statement-identical comparison was
  found within the explicitly recorded search;
- `unresolved`: the available evidence does not support a sharper verdict.

No row below uses search failure as proof of novelty. In particular, the audit
makes no first-publication or first-formalization claim.

## 2. Local statement pins

| Item | Verification level used here | Local artifact SHA-256 | Principal implication audited |
|---|---|---|---|
| T20 | `machine-checked` | `202d6db7dfc2f19db81c3cb96b856d36969652e54099c43e0d51b6ab62913126` | Every finite base-10 word occurs in the floor-digit stream of `x >= 0` iff `fract(10^n x)` is dense in `[0,1]`; specialize to pi. |
| T26 | `machine-checked` | `3825d0dcb5bd4d22ffa3cd8853db1bbf79c2ad1faa4ff0f1db96dbf7efc11871` | Cancellation of every nonzero circle character implies continuous equidistribution, hence dense range; specialize conditionally through T20 to V1. |
| T27 | `machine-checked` | `fd9c730e411dd7fb12b5b1a103c683238595c68bbea0f06af0250b4d13a8ee4e` | A common finite bound for frequencies `0 < |h| <= H`, plus `H B + N/((H+1)L^2) < N`, forces a hit in every interval of length `L`; specialize to decimal cylinders. |
| T28 | `literature-checked` | `4845c8661303b873bc4bb38dc8ee1005695fdd62b1fe4d16b36eaee61244abbd` | Metric lacunary estimates instantiate T27 for almost every initial point, but do not instantiate it at the named point pi. |
| T29 | `machine-checked` | `36bccfb678a9e3452bb4321a518541d2d0c9af79b995e1305ae47bc35d11c171` | A globally missing length-`k` word forces one fixed nonzero frequency `|h| <= 2*10^(2k)` with a linear exponential-sum lower bound along unbounded prefix lengths. |
| T30 | `proof sketch` | `30526b8de0fa901d7fc24323ab98b1ee911d0c307322a3be023464e6c5196866` | The T30 note argues conditionally that `not V1` yields a base-10-invariant weak-* empirical limit retaining a nonzero fixed Fourier coefficient. |
| T32 | `machine-checked` | `a4220356635f89e96724ce4a60167c09026bfcff98b6e34073f0a52794259a34` | Omitting one nonempty length-`k` decimal word gives `p(mk) <= (10^k-1)^m` and entropy at most `log(10^k-1)/k < log 10`; specialize from `not V1`. |
| T33 | `machine-checked` | `b4125d0c3cc2b05722721bbbda12747fbd8f1c95520ed3ea067bfc619b584e5b` | If exactly `r` symbols recur arbitrarily late, factor entropy is at most `log r`; entropy above `log 9` therefore implies V3, and `log 9` is sharp for an artificial nine-symbol stream. |

These normalized statements preserve the local quantifier order. In T29, for
example, the frequency is chosen before the arbitrary threshold on prefix
length. In T30, only one selected empirical limit is claimed to resonate.

## 3. Retrieved comparison sources

| ID | Source, stable locator, and retrieval URL | Retrieved file and SHA-256 |
|---|---|---|
| H96 | Peter Hertling, *Disjunctive Omega-Words and Real Numbers*, J.UCS 2(7), 1996, 549-568. DOI <https://doi.org/10.3217/jucs-002-07-0549>. Stable record <https://zenodo.org/records/6995264>. PDF <https://zenodo.org/api/records/6995264/files/jucs_article_27272.pdf/content>. | `sources/hertling-1996-disjunctive.pdf`, `49d3ac2b2a5f0b257dc926e2a5b770ab7be03dca5c40cea652417537d2cc7f51` |
| BRR68 | I. D. Berg, M. Rajagopalan, and L. A. Rubel, *Uniform Distribution in Locally Compact Abelian Groups*, Trans. AMS 133 (1968), 435-446. DOI <https://doi.org/10.1090/S0002-9947-1968-0227695-6>. PDF <https://www.ams.org/journals/tran/1968-133-02/S0002-9947-1968-0227695-6/S0002-9947-1968-0227695-6.pdf?download=1>. | `sources/berg-rajagopalan-rubel-1968.pdf`, `50cae4bd7ee487956f604117ffa9718bc03c690d5c9979cb671ef39158df8942` |
| R13 | Zev Rosengarten, *An Erdos-Turan Inequality for Compact Simply-Connected Semisimple Lie Groups*, arXiv:1305.2458v1. Stable arXiv DOI <https://doi.org/10.48550/arXiv.1305.2458>. PDF <https://arxiv.org/pdf/1305.2458v1>. | `sources/rosengarten-2013-erdos-turan.pdf`, `c035a7dfb38919fd5b6312f020178bfa481d70bfd881684c439a47904abd85f8` |
| EG55 | P. Erdos and I. S. Gal, *On the Law of the Iterated Logarithm. I*, Indagationes Mathematicae 17 (1955), 65-76. DOI <https://doi.org/10.1016/S1385-7258(55)50010-2>. PDF <https://www.renyi.hu/~p_erdos/1955-06.pdf>. | `sources/erdos-gal-1955-part1.pdf`, `a94e2560d886e4de674f678363c596276c73e0e06a492a866239543dee746931` |
| F08 | K. Fukuyama, *The Law of the Iterated Logarithm for Discrepancies of {theta^n x}*, Acta Math. Hungar. 118 (2008), 155-170. DOI <https://doi.org/10.1007/s10474-007-6201-8>. Repository <https://hdl.handle.net/20.500.14094/90003836>. PDF <https://da.lib.kobe-u.ac.jp/da/kernel/90003836/90003836.pdf>. | `sources/fukuyama-2008-geometric-discrepancy.pdf`, `59b263e7d74aa627606181646c75c02803c41d42af4d1780f7ff8de28f917266` |
| WN | Charles Walkden, *Ergodic Theory* lecture notes, University of Manchester, course MATH41112/61112. Stable author URL <https://personalpages.manchester.ac.uk/staff/charles.walkden/ergodic-theory/ergodic_theory.pdf>. | `sources/walkden-ergodic-theory-notes.pdf`, `875df70577cd3bcea0586ad258cb12f17c1e9c2400ef155ae640933e2c008b93` |
| MM18 | Christian Mauduit and Carlos Gustavo Moreira, *Complexity and Fractal Dimensions for Infinite Sequences with Positive Entropy*, Commun. Contemp. Math. 21 (2019), 1850068. DOI <https://doi.org/10.1142/S0219199718500682>. arXiv <https://arxiv.org/abs/1702.07698v2>. PDF <https://arxiv.org/pdf/1702.07698v2>. | `sources/mauduit-moreira-2018-complexity.pdf`, `421aa402a79cd79630cc2d763e8ad529a28017ec8114a133d2e690b447a9ea85` |
| MW08 | Brian Marcus and Susan Williams, *Symbolic Dynamics*, Scholarpedia 3(11):2923 (2008). DOI <https://doi.org/10.4249/scholarpedia.2923>. Article <http://www.scholarpedia.org/article/Symbolic_dynamics>. | `sources/marcus-williams-2008-symbolic-dynamics.html`, `543cac11bc8aa5beaa3ad12a555c01419ea34e70f11647bd174a1d9535e7a0dc` |

PDF quotations were checked after `pdftotext -layout`. The retrieved H96 scan
has imperfect font extraction, so quotations below follow the visually clear
printed text rather than its damaged ligatures.

## 4. T20: decimal words and orbit density

### Exact local implication

For `x >= 0`, every finite list over `Fin 10` occurs in the floor-based stream
`Real.digits x 10` iff, for every `y in [0,1]` and every `epsilon > 0`, some
`fract(10^k x)` is within `epsilon` of `y`. T20 then identifies the `x = pi`
instance with canonical V1. It proves neither side unconditionally.

### Published comparison and quotation

H96, Definitions 1.1 and 1.2, printed p. 549:

> "An omega-word p in Sigma^omega is disjunctive if every finite string in
> Sigma^* occurs as a subword in p."

> "A real number x in [0,1) is said to be disjunctive ... to base b if
> nu_b(x) in Sigma_b^omega is disjunctive."

H96 also defines `nu_b(x)` as the unique base-`b` expansion containing
infinitely many digits different from `b-1`. For a digit stream `p`, the basic
cylinders are the sets of streams with a fixed finite prefix. Therefore

```text
p disjunctive
iff every cylinder contains some shift sigma^n(p)
iff {sigma^n(p) : n >= 0} is dense in the one-sided full shift.
```

Under positional evaluation, shifting digits satisfies
`nu_b(sigma^n p) = fract(b^n nu_b(p))`; the images of length-`m` cylinders are
the half-open base-`b` mesh intervals of length `b^-m`. These identities give
the exact comparison with T20. T20's extra work is the floor-digit convention,
terminating-expansion bookkeeping, and metric approximation to the endpoint
`1`.

### Verdict

**standard specialization.** The mathematical equivalence is the standard
symbolic cylinder/shift coding of base expansion. No numbered source theorem
packaging T20's exact floor-based endpoint formulation was found, but that
bounded non-match does not override the direct reduction above. The Lean
development has formalization value; no first-formalization claim is made.

## 5. T26: Weyl cancellation to V1

### Exact local implications

T26 assumes normalized exponential sums tend to zero for every nonzero integer
frequency. It concludes convergence of every continuous complex test-function
average to Haar mean, then dense circle range, then density of fractional real
representatives. For `x_k = 10^k*pi`, T20 turns this into conditional V1.

### Comparison theorem and quotation

BRR68, p. 437, defines uniform distribution by convergence against every
continuous complex-valued function to Haar integral and states:

> "Theorem (Weyl criterion). If G is a compact Abelian group, then {g_v} is
> uniformly distributed in G if and only if, for each nontrivial character
> chi, <chi,{g_v}> = 0."

BRR68, p. 440 in the proof of Theorem 2, explicitly records the next step:

> "... {phi_H(g_v)} is dense in G/H, since {phi_H(g_v)} is u.d. in G/H and
> we recall that in a compact group a u.d. sequence must be dense."

Take `G = R/Z`; its nontrivial characters are `x |-> exp(2*pi*i*h*x)` for
nonzero `h in Z`. This is exactly T26's circle hypothesis and continuous-test
conclusion. Dense range is the quoted consequence. Passing between the circle
and `fract` representatives and invoking T20 are elementary specializations,
not new analytic input.

### Verdict

**standard specialization** for cancellation to continuous equidistribution;
the density and conditional-pi conclusions are known consequences of that
specialization. The exact Lean route through Fourier density and endpoint
representatives has formalization value but no established priority.

## 6. T27: finite exponential certificate

### Exact local implication

For `N > 0` points in `[0,1)`, suppose every integer frequency
`0 < |h| <= H` has unnormalized sum norm at most `B`. T27's Fejer-kernel proof
gives a one-sided interval-count lower bound and coverage whenever

```text
H*B + N / ((H+1)*L^2) < N.                       (T27-CERT)
```

The decimal specialization sets `L = 10^-k` and then uses T20's cylinders.

### Comparison theorem and quotation

R13, Definition 1.4 and Theorem 1.5, printed p. 2:

> "We define the discrepancy of a, denoted D(a), by
> D(a) := sup_I |(1/N)|{1 <= i <= N : a_i in I}| - m(I)|, where the supremum
> is over all intervals I in S^1."

> "Theorem 1.5 (Erdos-Turan Inequality). Let a = {a_i}_{i=1}^N be a sequence
> of points in S^1. Then for some absolute constant C, and every positive
> integer k,
> D(a) <= C(1/k + sum_{0<|n|<=k} (1/|n|) |(1/N)sum_i e(n a_i)|)."

If an interval of length `L` is missed, the quoted definition gives
`D(a) >= L`; hence any upper bound strictly below `L` forces coverage. This is
the same finite Fourier-to-coverage mechanism. It does not reproduce
`(T27-CERT)` constant-for-constant: R13 has an unspecified absolute constant
and harmonic weights, whereas T27 uses one common `B` and the explicit Fejer
tail `1/((H+1)L^2)`.

### Verdict

**no match found in the bounded search** for T27's exact displayed constants
and hypothesis packaging. This verdict is explicitly limited to the searches
in Section 12. The broader mathematical mechanism is standard Erdos-Turan
discrepancy theory, and the audit does not infer mathematical novelty from the
constant-level non-match. The machine-checked explicit certificate is useful
as a formal quantitative interface.

## 7. T28: metric lacunary estimates do not specialize to pi

### Exact audited implication

For each fixed word length and a sufficiently large fixed frequency cutoff,
classical metric lacunary bounds eventually satisfy T27 for almost every
initial point. Their exceptional-null-set quantifier does not imply the bound
at the named point `x = pi`.

### Comparison theorems and quotations

EG55, main theorem, printed p. 65:

> "Let n_1 < n_2 < ... be an infinite sequence of positive numbers,
> satisfying the lacunarity condition n_(v+1)/n_v >= q > 1. Then
> limsup |sum_{j=1}^N exp(2*pi*i*n_j*x)| / sqrt(N log log N) = 1
> for almost all x."

For fixed positive `h`, set `n_j = h*10^(j-1)` and `q = 10`. Finite
intersection handles fixed `1 <= h <= H`, and negative frequencies follow by
conjugacy. Thus one common `B_N = O(sqrt(N log log N))` works eventually for
almost every `x`; with fixed `H+1 > 10^(2k)`, `(T27-CERT)` eventually holds.

F08, Theorem and Corollary, manuscript pp. 1-2 / journal pp. 155-156:

> "For theta > 1, Sigma_theta := limsup N D_N({theta^k x}) /
> sqrt(2N log log N) = limsup N D_N^*({theta^k x}) /
> sqrt(2N log log N) = sup_{0<=a<1} sigma_{theta,0,a}, a.e. x."

> "When p >= 4 is even and q = 1,
> Sigma_theta = (1/2)sqrt((p+1)p(p-2)/(p-1)^3), a.e."

The latter gives the exact geometric discrepancy constant at `theta = 10`,
again only almost everywhere.

### Verdict

**known consequence.** The almost-everywhere instantiation follows by the
displayed parameter substitution and finite intersection. The failure to
specialize a conull assertion to pi is a quantifier fact, not a negative
literature or novelty claim. T28 supplies no fixed-pi certificate.

## 8. T29: omitted word to fixed-frequency resonance

### Exact local implication

If one length-`k` decimal cylinder is missed for all prefix lengths, T29 first
obtains, for every positive `N`, some frequency in the fixed finite set
`0 < |h| <= H(k)` with a linear lower bound. Finite pigeonhole then chooses one
`h` before the arbitrary threshold `B`, yielding arbitrarily large resonant
lengths. Its explicit constants are `H(k)=2*10^(2k)` and
`epsilon(k)=1/(8*10^(2k))`.

### Comparison and implication match

Apply R13 to a missed interval of length `L`. Since `D(a) >= L`, choosing
`H > C/L` in the quoted theorem gives

```text
max_{0<|h|<=H} |S_N(h)|/N
  >= (L/C - 1/H) / (2 * sum_{h=1}^H 1/h) > 0.
```

The set of eligible frequencies is finite. If every `N` has an eligible large
coefficient, at least one frequency occurs for infinitely many `N`; sorting
those lengths gives `exists h, forall B, exists N >= B`. This exactly matches
T29's significant quantifier order. R13 does not supply T29's constants;
those are a formal contrapositive of T27's explicit certificate.

### Verdict

**known consequence.** Missing interval to bounded-frequency resonance and
fixing a subsequential frequency are direct consequences of finite
Erdos-Turan plus finite pigeonhole. No standalone theorem with T29's exact
constants was found in the bounded search, but this is not treated as novelty.

## 9. T30: invariant resonant empirical limit

### Exact status and implication

T30 is not a Lean theorem. The T30 note argues, conditional on `not V1` and
T29, that a selected sequence of resonant empirical measures on `R/Z` has a
weak-* subsequential limit invariant under multiplication by ten, and that the
same fixed character has a nonzero Fourier coefficient in the limit. Every
conclusion in this section about T30 is conditional on that unverified note's
argument.

### Comparison theorem and quotation

WN, Theorem 7.5.1 and its proof, printed p. 69:

> "Let T : X -> X be a continuous mapping of a compact metric space. Then
> there exists at least one T-invariant probability measure."

The proof fixes an arbitrary probability measure `nu`, defines
`mu_n = (1/n) sum_{j=0}^{n-1} T_*^j nu`, and says:

> "Since M(X) is weak* compact, some subsequence mu_(n_k) converges ... to a
> measure mu in M(X). We shall show that mu is in M(X,T)."

It then displays the endpoint telescoping estimate bounded by
`2 ||f||_infinity / n_k`, which tends to zero. Taking `nu = delta_x` gives
precisely the selected orbit-empirical limit needed by T30; the same proof
applies after first restricting to T29's increasing resonant lengths. For the
fixed continuous character `chi_h`, weak-* convergence gives
`integral chi_h dmu_N -> integral chi_h dmu`; continuity of complex norm
preserves a closed lower bound `>= epsilon`. No converse follows, and invariant
measures with nonzero Fourier coefficients are commonplace.

### Verdict

**known consequence.** The invariance component is WN Theorem 7.5.1 and the
resonance retention is immediate weak-* continuity for one fixed bounded
continuous character. This literature verdict does not upgrade T30 beyond
`proof sketch` and proves nothing about V1 or V3.

## 10. T32: omitted word and entropy deficit

### Exact local implication

If a stream over ten symbols omits one nonempty word of length `k`, T32 proves
`p(mk) <= (10^k-1)^m`, extends the estimate to its full positive-length limsup
entropy, and obtains an upper bound strictly below `log 10`. Literal `not V1`
supplies such an omitted nonempty word.

### Comparison theorem and quotation

MM18, equation (1), PDF p. 2:

> "For any w in A^N and for any (n,n') in N^2 we have
> L_{n+n'}(w) subset L_n(w)L_{n'}(w) so that
> p_w(n+n') <= p_w(n)p_w(n')."

MM18 then states, PDF p. 3:

> "the sequence ((1/n) log p_w(n))_{n>=1} converges to
> inf_{n>=1} (1/n) log p_w(n)."

If one length-`k` word is absent over a `q`-symbol alphabet, then
`p_w(k) <= q^k-1`. Iterating the quoted inequality yields
`p_w(mk) <= (q^k-1)^m`; taking the quoted entropy infimum yields
`h(w) <= log(q^k-1)/k < log q`. This is T32 with `q=10`. MM18 Claim 1.4 also
records the general principle that a fixed-length complexity deficit forces a
strictly smaller exponential growth rate.

### Verdict

**standard specialization.** T32's mathematical bounds are direct decimal
specializations of the published submultiplicativity and entropy formula. Its
exact finite-type encoding and full limsup proof have formalization value;
priority as a Lean formalization was not established.

## 11. T33: recurrent alphabet and the sharp V3 threshold

### Exact local implication

For a decimal stream, let `r` be the number of digits occurring arbitrarily
late. Finiteness gives a cutoff `C` after which only those `r` digits occur.
T33 counts `p(n) <= C+r^n`, concludes entropy at most `log r`, and derives
`entropy > log 9 -> V3`. It constructs a non-pi universal stream on digits
`0,...,8` with entropy exactly `log 9` and no digit `9`.

### Comparison statements and implication match

MW08 defines symbolic entropy by block growth:

> "Among the most important invariants is topological entropy, defined as
> h(X)=lim_{N->infinity} log|B_N(X)|/N."

It then states:

> "For the full r-shift X, |B_N(X)|=r^N, and so h(X)=log r."

MM18 supplies the corresponding one-word language formula and subadditive
limit quoted in Section 10. Once the finite cutoff `C` is fixed, a length-`n`
factor either starts before `C` (at most `C` factors) or is a word over the
recurrent alphabet (at most `r^n` factors). Hence

```text
p(n) <= C+r^n <= (C+1)r^n,
h <= log r.
```

If decimal V3 fails, at most nine digits recur, so `h <= log 9`. Conversely,
`h > log 9` forces all ten digits to recur and hence V3. A universal word over
nine symbols has the full nine-shift language, so the quoted full-shift formula
gives entropy `log 9` while decimal digit `9` is absent.

### Verdict

**known consequence.** No source with T33's exact recurrent-symbol wording was
located, but its implication follows from the displayed finite-cutoff count
and standard block-growth entropy statements. The bounded wording-level
non-match is not evidence of novelty. The Lean construction supplies a sharp,
formally separated non-pi example.

## 12. Bounded search record

Search date: 2026-08-01. Raw retained responses are in
`bounded-searches-20260801.tar.gz`, SHA-256
`bc9126b7eee75f4662dc5a47883d414eb40faab85e15360ff6aa225eb6279ef9`.
The archive contains exactly the nine response files reproduced by
`reproduce.sh search OUTPUT_DIRECTORY`.

| Family | Database, exact query, and bound |
|---|---|
| T20 | Crossref REST, `query.bibliographic=disjunctive sequence dense shift orbit base expansion`, first 20 selected records; OpenAlex, full-text metadata search with the same terms, first 20. |
| T26 | Crossref REST, `query.bibliographic=Weyl criterion uniform distribution compact abelian group`, first 20; OpenAlex same terms, first 20. |
| T27/T29 | Crossref REST, `query.bibliographic=Erdos Turan inequality interval coverage exponential sum discrepancy`, first 20; arXiv API `all:"Erdos-Turan inequality"`, first 20. |
| T30 | OpenAlex, `empirical measure weak limit invariant continuous map compact`, open-access filter, first 20. Direct source checks followed. |
| T32/T33 | Crossref REST, `query.bibliographic=factor complexity omitted word entropy recurrent alphabet`, first 20; OpenAlex same terms, first 20. |

Candidate selection also followed references in the retained primary sources and
directly checked the listed DOI/repository records. Search-engine probes for
exact phrases were rate-limited or challenge-blocked and therefore are not
counted as negative evidence.

Mathlib was searched at the installed source tree on 2026-08-01. Exact searches
for `factorEntropy`, `canonicalFactorComplexity`, `FirstFrequencyBound`,
`WeylCancellation`, and `disjunctive` returned no declarations. The existing
`Mathlib/Dynamics/SymbolicDynamics/Basic.lean` provides cylinders, occurrence,
and language infrastructure but no matching entropy or omitted-word theorem.
A broader grep for equidistribution and Weyl terminology found no theorem
matching T26. This is only a search of the installed mathlib snapshot, not all
Lean repositories or historical versions.

Explicit limits of the negative search:

- no subscription search of MathSciNet or zbMATH;
- no exhaustive citation-chain or historical-priority review;
- no exhaustive GitHub, LeanSearch, Loogle-history, Isabelle, Coq, or Agda search;
- metadata APIs were capped at the first 20 ranked records per query;
- exact constants were checked only in the retained candidate sources;
- exact comparison quotations were limited to inspectable retained files.

Therefore `no match found in the bounded search` means exactly those bounds and
nothing stronger.

## 13. Conclusions

| Item | Mathematical verdict | Formalization value without priority claim |
|---|---|---|
| T20 | `standard specialization` | Exact floor digits, cylinder endpoints, shift identity, and pi bridge. |
| T26 | `standard specialization` | Compact-circle Weyl proof and real representative endpoint handling. |
| T27 | `no match found in the bounded search` for exact constants; standard mechanism | Explicit machine-checked one-sided Fejer certificate. |
| T28 | `known consequence` | Precise quantifier and parameter audit preventing an invalid specialization to pi. |
| T29 | `known consequence` | Explicit constants and formally correct fixed-frequency quantifier order. |
| T30 | `known consequence`, conditional on an unverified `proof sketch` | Inspectable measure-theoretic packaging; not machine-checked. |
| T32 | `standard specialization` | Full-limsup Lean implementation and exact T7 bridge. |
| T33 | `known consequence` | Recurrent-alphabet cutoff count and sharp non-pi Lean construction. |

The package's strongest supported value is formal and organizational: exact
interfaces, quantifier discipline, explicit constants, and machine-checked
reductions. The audit finds no justified claim that these items resolve V1 or
V3, and no justified claim of new mathematical content.

## 14. Reproduction

From a directory containing only the delivered artifacts:

```sh
chmod +x reproduce.sh
./reproduce.sh verify
./reproduce.sh extract /tmp/t35-text
./reproduce.sh search /tmp/t35-search-fresh
./reproduce.sh fetch /tmp/t35-source-fresh
```

`verify` checks every retained artifact hash and the canonical source hash.
`extract` reruns `pdftotext -layout`. `search` repeats all nine bounded API
requests. `fetch` redownloads all source URLs and prints fresh hashes. API
rankings, repository encryption, and publisher files
may change; a fresh mismatch is a detectable source-version change, not license
to alter the retained pin.

The 2026-08-01 adversarial replay completed all four modes. The AMS, Zenodo,
arXiv, and Erdos-Gal downloads reproduced byte-for-byte. Kobe returned a
dynamically different Fukuyama PDF with SHA-256
`f7d87430cd1d65a3d61d7083ce4c4bece5d40a0f9d01d2868e73c3557717459b`;
its extracted theorem and corollary at lines 109-130 remained textually the
same, although the full extracted-file hash also changed. Scholarpedia returned
a dynamically different HTML hash while retaining the quoted lines. All nine fresh search
requests succeeded. These observed mutations explain why the exact retained
bytes are vendored and hash-checked separately from live replay.
