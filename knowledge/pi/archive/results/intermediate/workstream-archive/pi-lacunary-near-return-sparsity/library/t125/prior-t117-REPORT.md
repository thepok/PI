# T117: Legendre subset-product pattern-cancellation audit

Audit date: 2026-08-10 UTC.

Claim labels are load-bearing. Statements attributed to the two pinned primary
sources are `literature-checked`. Sections 5--8 are new `proof sketch`
deductions from those statements. The bounded replay is an `experiment`; it
checks hashes, formulas, and finite examples, not the universal deductions.
The PI-TRACE premise in Section 9 is a `conjecture`, not a property of pi.

```text
PRIMARY_SOURCE_COUNT: 2
PRIMARY_SOURCE_CAP: 6
RETAINED_FAMILY_COUNT: 1
RETAINED_FAMILY_CAP: 2
TERMINAL_VERDICT_COUNT: 1
SUCCESSOR_COUNT: 0
```

This report proves no statement about pi, canonical A1, C1, C2, normality of
pi, decimal factor complexity, or decimal digit occurrence.

## 1. Immutable statement and normalized scope

The delivered `canonical_statement.txt` is a byte-exact copy of
`knowledge/pi/statements/pi-lacunary-near-return-sparsity.txt`. Its SHA-256 is

```text
cbf56699b651aeb69301265763e38da44feb59c6fd955d2280887e8c06c6a2f8
```

For integers `n,N>=1`, the canonical count is

```text
Q_pi(n,N) = #{(i,j) in {0,...,N-1}^2:
               ||(10^i-10^j)pi||_(R/Z) < 10^(-n)}.
```

Pairs are ordered, the diagonal is included, and the circle inequality is
strict. The open quantifier order is

```text
for every integer A>=1 there exists n0>=1 such that
for every integer n>=n0 there exists N>=1 with
A*n*Q_pi(n,N) <= N^2.
```

T117 changes the point, alphabet, period, and collision predicate. It studies
a binary finite-field sequence indexed by `F_p` and exact equal binary words.
It is therefore only an A13/A14 related model. Exact binary-word equality is
not strict circle near return for the decimal orbit of pi.

Normalized ambiguities for this audit:

1. `log_2` is the base-two logarithm; `log` in cited source formulas is the
   natural logarithm.
2. A source is counted once even though its PDF and line-addressable text
   derivative are both delivered.
3. A family means one rule indexed by all odd primes, not one candidate per
   prime.
4. The Legendre symbol is extended by `chi_p(0)=0`. The binary symbol at zero
   is declared to be zero; it is not silently treated as a sign.
5. A cyclic start ranges over all of `F_p`. A linear start is an integer in
   `{0,...,p-m}` and does not wrap around the period.
6. Pattern estimates are pointwise in every word, not averaged over words,
   primes, shifts, or patterns.
7. The declared universal range is `1<=m<=p`. The growing range used for the
   scale test is the smaller range `m=floor(kappa*log_2 p)` with fixed
   `0<kappa<1/2` and sufficiently large `p`.

## 2. Bounded three-lane source audit

The search stopped after two full primary papers. They cover all requested
lanes without filling the cap.

| ID | Lane | Source | Exact use |
|---|---|---|---|
| S1 | symbolic collision theory and structured character sums | Mauduit--Sarkozy, *On finite pseudorandom binary sequences I: Measure of pseudorandomness, the Legendre symbol* | exact pattern statistic, pattern-to-correlation expansion, Legendre family, complete character-sum bound, shifted-product squarefreeness |
| S2 | arithmetic Fourier decay over finite fields | Weil, *On Some Exponential Sums* | conductor/root mechanism and square-root estimate underlying the finite-field character bound |

S1 is load-bearing. S2 is the primary historical mechanism pin; no stronger
constant is imported from it than S1 states explicitly. `SOURCE_PINS.md` gives
URLs, hashes, pages, equations, and derivative lines. `SEARCH_LOG.md` records
the bounded searches and the inaccessible Ding lead.

### 2.1 Literature-checked source statements

S1 printed pp. 368--369, equations (2.1), (2.4), and Definition 1, defines the
number of occurrences of every fixed sign word and compares it with the
uniform main term. Printed pp. 370--371, Proposition 1 and its proof, expands
the exact word indicator into all nonempty subset correlations and proves

```text
N_k(E_N) <= max_(1<=t<=k) C_t(E_N).                       (2.1)
```

S1 printed p. 373, Theorem 1, defines the length-`p-1` Legendre sign sequence
and proves for `p>p0` and every integer `1<=k<p`

```text
Q_k(E_(p-1)) <= 9*k*sqrt(p)*log p.                        (2.2)
```

Printed pp. 373--374, Theorem 2, Corollary 1, and Lemmas 1--3 state the
character hypotheses and the complete hybrid bound. In particular, if a
degree-`d` polynomial has at least one root of odd multiplicity, then for the
quadratic character it is not a scalar times a square; Lemma 3 with additive
frequency zero gives the complete estimate

```text
|sum_(x in F_p) chi_p(f(x))| <= d*sqrt(p).                (2.3)
```

Printed pp. 375--376, equations (6.1)--(6.3), takes products of distinct
shifted linear factors and checks that there is no multiple root before
applying the character estimate.

S2 printed pp. 205--206 defines the multiplicative character, conductor, and
distinct root divisor, then equations (4)--(5) give a square-root bound whose
constant is linear in conductor and the number of roots. Printed p. 207 gives
the polynomial hybrid specialization. The delivered text derivative is
approximate transcription of an image scan; the PDF pages are authoritative.

## 3. T89--T116 novelty and exclusion table

This table is comparison memory, not a premise. `literature-checked` applies
only to source claims in the named reports; their new deductions remain
`proof sketch` unless a machine-checked file is identified. The accepted T114
and T116 reports are vendored byte-exactly and used only as fingerprint
comparators.

| Item | Inspection pin and level | Normalized fingerprint | Legendre comparison |
|---|---|---|---|
| T89 | report SHA `ad90a5a5084f7ef19f4fce052ae99330f0cab9103f2942ee164d713de2a8b5b9`; sources checked, deductions sketch | Kempner resonance and collision-rich decimal Thue--Morse | no finite-field character or all-subset bound |
| T90 | `730c5cdaf154bd375084a243fc82ebf6ab4ce2c1e234baf43515d4aaea34cfc0`; sources checked, transfers sketch | explicit expanding-map points and discrepancy | aggregate discrepancy, not period-`p` subset products |
| T91 | `a684f15960a176f37ee2e8e853313e05e0e2f8de9674be2fcd744f59fe62573e`; unverified sketch | substitution/paperfolding collision recurrences lose all-start mass | no overlap |
| T92 | report `155f1a4652f125bcf48e668315b05199a6077a943bf19f714e1e1ad02d9e19c1`; Lean theorem checked | constant-stream short-to-remote charging | no overlap |
| T93 | `2ff685b20920f5a2d71db2b8a300ce8c2762152c3d4b2c59236b160ed812f8ae`; sketch | Stoneham repeated modular residues | repetition, not cancellation |
| T94 | `f399dfac1990b3cc4a6c9e69127a1ceff22356c6b656ec2e3a1b9045be6efa10`; sketch/experiment | paperfolding tensor profile | no overlap |
| T95 | `08baad91851c1d25ceaa82f86cbe8b728ca2c063f31f01f83c5fa96aea45d8cb`; sketch | universal exact-word charging | no overlap |
| T96 | `de8940fd7927a20d88626cec7ae8b411cd2788c1fdecb762496a72c8f18019aa`; sketch | prime-family Stoneham skeleton | no overlap |
| T97 | `fb3c58a436d173902ccf3577dc02d1702403f681d6cc08a39481e1c73cd31a8e`; sketch/experiment | paperfolding diagonal collision asymptotics | no overlap |
| T98 | `b6b8d30499543fadf5be200b85afe3929dcba5b7a7d96061476965060c589f57`; sketch | conditional transport of exact-word charging | no overlap |
| T99 | `9778fd0fdc3151b0e3f8888afdb1d1049347e926d266f2981e7daa3bc44af2b4`; sketch | exceptional-prime Stoneham repetition | no overlap |
| T100 | report `7328d1730a68b820441f4e6c1eb9c4bbb99abb34193dbcc1270f6990a8c905fb`; machine-checked Lean | universal finite-word charging | no overlap |
| T101 | `ddd24794d6e6795a4aa466819782aa63a6578d70746ce4d592bb18ef644c243e`; sketch/experiment | paperfolding has only `O(1/n)` relative successor loss | no overlap |
| T102 | `49a63d0003102728766a41e026400f3bc69e9baeb42e66338510bcbecc1d6304`; sketch | coprime Stoneham order profiles | no overlap |
| T103 | `ed690a31fbc19d08c817bcb2558ec259788e37d4f8243261ece1b9eafbbb5df0`; sources checked, deductions sketch | Toeplitz periodic-hole towers | no overlap |
| T104 | `2dee0c91ce8480785a851df4aad06e0ab65f92e647fa7f67605b868129fc16d5`; sources checked, deductions sketch | torus orthogonality and ambient/nonlinear Fourier decay | generic cancellation only; no period-`p` word expansion |
| T105 | `ff63d5a956765beda402cc36e953a6f678ad1bf900254e6e2e8a20326842ed9f`; sources checked, deductions sketch | additive energy, BSG, and modular geometric sums | character vocabulary only; no shifted subset products |
| T106 | Lean SHA `824971b102f33b41f6c2f79ad616cc03b1ce83d59aec5edafa836f2cafa89f61`; machine-checked | finite branching resonance trees | no overlap |
| T107 | Lean SHA `45cb809d65c38b866ad7c46c913d617c61f8e97e777ccdec8ed9645e4982ae28`; machine-checked | averaged triangular boundary/Fourier defect | target interface only, no Legendre construction |
| T108 | Lean SHA `97f6333ee777b45b842530876ac5e6d29309cfe0987a1ce669690c86c8e5caee`; machine-checked | three-cylinder transport of exact-word charging | no overlap |
| T109 | rejected report SHA `6b4f27464b76c67ea6fe41990f9ed6d3242c8c763b880fb4862fbac16f3ffcdf` | Markov perturbation, shadowing, Wasserstein stability; rejected for treating sufficient tests as necessary | no overlap; its rejection warning is obeyed |
| T110 | `4eaa088ecb7ea8936d5c35d1eefb66027b376a020c8e76f4a2b91c012a3cb668`; sources checked, deductions sketch | fixed-order Gowers decay and q-multiplicative polynomial phases | nearest abstraction, but no growing all-subset Legendre expansion |
| T111 | `89eae292ac15699fd7175b879189d6eb5560fd692029f8a9dbdc1093583156d8`; sources checked, deductions sketch | de Bruijn odd-code exact separation | no overlap |
| T112 | `72884fc7d8d594cfd2f380cafde121c541c1aa316badf054ac143bb102abcefa`; sources checked, deductions sketch | carry local limits and finite-state twisted operators | pointwise-sum similarity only; no all-word estimate |
| T113 | `30ff535624185d37981311d2f1e2a072d300221bec3f049351e5cae1026ed445`; unverified sketch, sources checked | variable-threshold existential avoidance | no overlap |
| T114 | accepted report SHA `db21ac7d0a7845264c727132293db149a06a832d6f67700fd9ceb0f69a142cca`; source statements literature-checked, determinant specializations and exponent comparisons proof sketch | interpolation determinants have the wrong height sign; literal multiples of pi are rank-deficient; fixed-lag recurrence does not cap aggregate occupancy | no overlap: T117 uses squarefree shifted subset products and pointwise character sums, not determinant nonvanishing, rational-rank growth, or a `D_N` occupancy contradiction |
| T115 | `29cd0707df354aef8f50e4dfa4b9a780b863d93aef26cebdc4cbb8488ee27a36`; sources checked, deductions sketch | base-ten substitution Riesz recursion has a persistent ray | no overlap |
| T116 | accepted report SHA `573011bda281022483a113829138112494b73d667323c30aa2a0ef03bba32cd1`; source statements literature-checked, selector and collision deductions proof sketch, replay experiment | effective weighted-tree avoidance selector and odd-code de Bruijn exact separation for computable sibling points | adjacent related-model endpoint but distinct mechanism: T116 selects one infinite point by forbidden-weight budgets or exact coding, while T117 counts every word in each finite period by pointwise subset-product cancellation; no selector or fixed-point transfer is imported |

No available prior item contains the complete chain

```text
quadratic character period
  -> every shifted subset product is squarefree
  -> pointwise complete Weil bound for every subset
  -> uniform growing-m word counts
  -> explicit block-collision upper bound.
```

However, S1 already contains the central pattern-from-correlation fingerprint
for Legendre sequences in the research literature. T117 therefore claims a new
program comparator and an explicit collision calculation, not a novel
Legendre pattern theorem.

## 4. Sole retained family and exact pattern statistic

Let `p` be an odd prime and let `chi_p:F_p->{-1,0,1}` be the quadratic
character, extended by `chi_p(0)=0`. Define the period-`p` binary Legendre word

```text
L_p(x) = 1 if chi_p(x)=1, and L_p(x)=0 otherwise.          (4.1)
```

Thus `L_p(0)=0`. For an integer `m` with `1<=m<=p` and a word
`w=(w_0,...,w_(m-1)) in {0,1}^m`, define the cyclic pointwise count

```text
A_(p,m)(w)
  = #{x in F_p: L_p(x+j)=w_j for every 0<=j<m}.           (4.2)
```

All additions inside (4.2) are in `F_p`. The bound below quantifies over every
odd prime `p`, every `m` in the declared range, and every one of the `2^m`
words separately.

Only this family is retained. General multiplicative characters and higher
degree trace-function words were screened out: their alphabets, exceptional
sets, and conductor constants require separate definitions without changing
the cheapest quadratic test.

## 5. Pointwise subset-product calculation

This section is a `proof sketch`, written in full.

Put `epsilon_j=2*w_j-1` and

```text
Z_m={-j in F_p:0<=j<m}.
```

The range `m<=p` makes the shifts distinct, so `|Z_m|=m`. For `x` outside
`Z_m`, every character value is a sign and the exact indicator is

```text
1_[pattern w at x]
  = 2^(-m) product_(0<=j<m) (1+epsilon_j*chi_p(x+j)).      (5.1)
```

At each of the `m` exceptional positions the left side is a zero-or-one
indicator while the surrogate right side lies in `[0,1]`. Therefore replacing
the indicator by (5.1) at every `x` costs at most `m` in absolute value.

Expand the product. For a nonempty subset `S` of `{0,...,m-1}`, put

```text
f_S(X)=product_(j in S)(X+j).                              (5.2)
```

If `d=|S|`, then `f_S` has degree `d`, exactly `d` distinct roots, and every
root multiplicity is one. It is not a scalar times a square. The quadratic
character is nonprincipal because `p` is odd. Thus every hypothesis of S1
Corollary 1 and Lemma 3 is met, pointwise for this `S`, and

```text
|sum_(x in F_p) chi_p(f_S(x))| <= d*sqrt(p).               (5.3)
```

The empty subset contributes exactly `p`. Since

```text
sum_(d=1)^m binom(m,d)*d = m*2^(m-1),                     (5.4)
```

the triangle inequality over all nonempty subsets gives

```text
|A_(p,m)(w)-p*2^(-m)| <= E(p,m),                          (5.5)

E(p,m) = m + (m/2)*sqrt(p),

for every odd prime p, every 1<=m<=p, and every w in {0,1}^m.
```

This is uniform over words and subsets. It is not an average over `w`.

### 5.1 Hypothesis ledger

| Required check | Discharge |
|---|---|
| character nontriviality | the quadratic character on `F_p^*` has order two for odd prime `p` |
| subset-polynomial degeneracy | distinct shifts under `m<=p` make every `f_S` squarefree; every nonempty `S` has odd root multiplicities |
| conductor/root growth | S1 Lemma 3 costs at most `d*sqrt(p)` for a degree-`d` subset; summing all normalized subset costs gives `(m/2)*sqrt(p)` |
| exceptional positions | exactly the `m` values `x=-j`; total deterministic cost at most `m` |
| pointwise quantifier | (5.3) is applied to each subset and (5.5) holds for each word |
| cyclic endpoints | included in `A_(p,m)`; linear removal is handled separately in Section 7 |

The bound is deliberately not sharpened to `(d-1)*sqrt(p)`: the pinned S1
Lemma 3 states the sufficient `d*sqrt(p)` constant, and no unstated stronger
version is needed.

## 6. Direct literature comparison

S1 already gives a noncyclic companion. Its Legendre sign sequence has length
`p-1`, excludes the zero symbol, and uses the `p-m` starts of a length-`m`
word. Combining S1 Proposition 1 with Theorem 1 yields, for `p>p0` and
`1<=m<p`, pointwise in every sign word,

```text
|T(E_(p-1),p-m,w)-(p-m)*2^(-m)|
  <= 9*m*sqrt(p)*log p.                                   (6.1)
```

The two inputs to (6.1) are `literature-checked`; their displayed combination
is a `proof sketch` deduction, not a verbatim source theorem. Equations
(5.1)--(5.5) are likewise a new proof-sketch repackaging for the cyclic
binary-zero convention. They remove the incomplete sum's logarithm at the cost
of an explicit exceptional-position term.

This source comparison prevents a novelty overclaim: the broad assertion that
Legendre sequences have uniformly distributed short patterns up to a
logarithmic range is already in the literature. T117's useful addition is only
the exact cyclic convention, explicit `E(p,m)`, and collision calculation.

## 7. Error-to-collision calculation

Define the ordered, diagonal-inclusive cyclic equal-block count

```text
C_cyc(p,m)=sum_(w in {0,1}^m) A_(p,m)(w)^2.               (7.1)
```

Since the pattern classes partition all `p` cyclic starts,
`sum_w A_(p,m)(w)=p`. From (5.5),

```text
C_cyc(p,m)
  <= max_w A_(p,m)(w) * sum_w A_(p,m)(w)
  <= (p*2^(-m)+E(p,m))*p
  = p^2*2^(-m)*(1+2^m*E(p,m)/p).                          (7.2)
```

This deliberately uses a maximum, not an averaged discrepancy.

For the finite linear prefix, let

```text
N_lin=p-m+1,
B_(p,m)(w)=#{x in {0,...,p-m}:L_p(x+j)=w_j for 0<=j<m},
C_lin(p,m)=sum_w B_(p,m)(w)^2.                            (7.3)
```

The `m-1` cyclic starts `p-m+1,...,p-1` are removed. Hence
`0<=B_w<=A_w` and `sum_w B_w=N_lin`, with no hidden terminal loss. Therefore

```text
C_lin(p,m)
  <= N_lin*(p*2^(-m)+E(p,m))
  = N_lin*p*2^(-m)*(1+2^m*E(p,m)/p).                      (7.4)
```

Equivalently,

```text
C_lin(p,m)/N_lin^2
  <= [p/(N_lin*2^m)]*(1+2^m*E(p,m)/p).                   (7.5)
```

Equations (7.2)--(7.5) count ordered pairs and include every diagonal pair.
They are exact equal-word sibling statistics, not `Q_pi`.

## 8. Growing-range scale test

The required dimensionless error is exactly

```text
R(p,m)=2^m*E(p,m)/p
      = m*2^m/p + m*2^(m-1)/sqrt(p).                     (8.1)
```

Fix any real `kappa` with `0<kappa<1/2` and put
`m(p)=floor(kappa*log_2 p)`. For sufficiently large primes, `1<=m(p)<=p`,
`m(p)->infinity`, and `2^m<=p^kappa`. Thus

```text
R(p,m(p))
 <= kappa*log_2(p) * [p^(kappa-1)+(1/2)*p^(kappa-1/2)]
 -> 0.                                                    (8.2)
```

The endpoint `kappa=1/2` is not claimed: (8.1) then has a term of order
`m/2`, which does not tend to zero. Consequently the explicit Legendre model
passes this certificate's quantitative test on every fixed logarithmic range
strictly below one half.

For comparison, inserting the source's incomplete error from (6.1) also gives
`2^m*9m*sqrt(p)*log(p)/p ->0` for every fixed `kappa<1/2`.

## 9. Conjectural PI-TRACE premise and exact boundary

The following is stated only to expose the missing transfer.

**PI-TRACE (conjecture, not asserted).** There are fixed
`0<kappa<1/2`, odd primes `p_r->infinity`, depths `n_r->infinity`, and prefix
lengths `J_r<=p_r-m_r+1`, where `m_r=floor(kappa*log_2 p_r)`, together with
injective maps from the first `J_r` decimal-orbit starts of pi to linear starts
of `L_(p_r)`, such that every equal length-`n_r` decimal-block pair for pi maps
to an equal length-`m_r` Legendre-pattern pair.

Conditionally, this relation injection would bound that selected exact decimal
block-collision count by `C_lin(p_r,m_r)`. Nothing in S1 or S2 constructs the
maps, controls decimal carries, treats adjacent cylinders, or upgrades exact
block equality to strict circle near returns. Failure to construct PI-TRACE
would close only this proposed certificate, not the underlying fixed-pi
transfer. PI-TRACE is not C1, C2, or a claim about pi; it is an explicitly
conjectural sufficient coding premise.

The cheapest rejection test for any concrete PI-TRACE proposal is finite and
one-sided: exhibit one pair of pi starts whose decimal blocks are equal but
whose proposed image Legendre patterns differ. That falsifies the proposed
map. Failure to find such a pair is only an `experiment`.

## 10. Replay and scope firewall

From a directory containing only the delivered artifacts, run

```text
python3 verify_t117.py
sha256sum -c SHA256SUMS
```

The verifier checks the canonical and source hashes, source anchor locations,
both hard caps, the pins and status tokens in all 28 T89--T116 table rows, the
vendored T109 rejection and accepted T114/T116 reports, the subset-count
identity, exact finite Legendre pattern counts, exceptional positions, cyclic
and linear collision bounds, and sample values of (8.1). Its bounded
computations are `experiment` only. `raw_output.txt` records one replay.

No source states PI-TRACE or a theorem about the decimal orbit of pi. No finite
calculation proves a universal pattern estimate. The proof-sketch deduction is
confined to the explicit finite-field sibling.

TERMINAL VERDICT (1/1): **HOLD AS MODEL.** The Legendre family is a clean
pointwise algebraic-cancellation model and passes `2^m*E/p ->0` for every fixed
`kappa<1/2`. It is not developed as a new research theorem because S1 already
contains the central Legendre pattern-distribution mechanism, and it supplies
no fixed-pi transfer. There is no successor (`SUCCESSOR_COUNT: 0`).
