# T4: Pi-Specific Quantitative Literature Audit Against T3

Status: `literature-checked` on 2026-07-22 for the bounded corpus and exact
sources in `retrieval_manifest.json`. This is not an exhaustive literature
claim and does not prove or disprove C1.

## 1. Target, Quantifiers, And Exclusions

The immutable canonical statement is
`knowledge/pi/statements/pi-quantitative-block-hitting.txt`, SHA-256
`ab000220813f99eb40cfdc2d7fdae4ea7796291852df43dce7e6bf317c247449`.
It asks for one integer `C >= 1` such that every positive length `k` and every
decimal word of length `k`, including leading-zero words, occurs contiguously
and is fully contained in the first `C*k*10^k` fractional digits of pi.

The comparison target is T3,
`UniformPiAnalyticCover.lean`, SHA-256
`473277f59fd2735f70c8ad03c26c0c7c024c1fd611a1375ab4afdba35d3cc2cc`.
Its exact certificate at each `k` requires witnesses `N,H : Nat` and `B : Real`
with

```text
0 < N,
N <= C*k*10^k,
|sum_(j<N) exp(2*pi*i*h*fract(10^j*pi))| <= B
  for every integer h != 0 with |h| <= H,
H*B + N*10^(2*k)/(H+1) < N.
```

One `C` must work for all `k`; `N,H,B` may depend on `k`. T3 then changes the
containment constant to `C+1`.

The search includes direct fixed-pi results on decimal or binary block
hitting, effective discrepancy or normality, BBP extraction, and normality
base transfer. It excludes ordinary spigot algorithms, results about
artificial constants, and generic almost-everywhere lacunary theorems.
Erdos-Gal, Philipp, and Fukuyama were already audited in accepted T28 (hash
`4845c866...`) and fail at the fixed input `x=pi`; they are not duplicated.
Finite digit calculations are retained only when they are direct candidates
and are labeled `experiment`, never evidence for C1.

Searches were the four exact finite API queries in `retrieval_manifest.json`,
plus citation-chain inspection of T6, T12, T19, T28, and the retained primary
papers. The API bounds are 30 Crossref records for each of two queries, 25
OpenAlex records, and 50 arXiv records. This documented corpus supports only
the negative finding below; unsearched literature is not classified.

Three T19 records were screened but excluded from the candidate matrix under
the declared scope: Stoneham's Theorem 5 concerns rational Wallis
approximants, not pi; Almkvist-Krattenthaler-Petersson attest a finite-position
decimal access algorithm, excluded with ordinary digit access; and
Aretxabaleta et al. analyze a finite-prefix billiards approximation, excluded
with finite prefix-generation mechanisms. Their exact quotations, source URLs,
and PDF hashes remain inspectable in the replay-verified T19 dependency, lines
80-121, 187-211, and 213-268 respectively. They were not silently treated as
failed fixed-pi distribution theorems.

## 2. Candidate Matrix

| ID | Exact result | Base and quantifiers | Effectivity and prefix dependence | T3 classification |
|---|---|---|---|---|
| BBP1997 | Theorem 1 gives the displayed base-16 series for pi; the abstract gives a `d`-th digit algorithm. | Hexadecimal/binary; computes a requested finite position `d`. | Nearly linear time and polylogarithmic space are asserted; no occurrence or frequency quantifier and no `N(k)`. | **Rejected:** no base-10 orbit estimate and no bound on any T3 exponential sum. |
| BC2001 | Hypothesis A plus Theorem 1.1 conditionally gives base-2 normality of pi; the displayed pi recurrence would conditionally give base-16 normality. | Base 16, hence base 2; asymptotic normality for every fixed word, conditional on one unproved dynamical dichotomy. | No discrepancy rate, effective threshold, growing-frequency uniformity, or prefix deadline. | **Rejected:** Hypothesis A is unmet; base is wrong; qualitative normality has no `N <= C*k*10^k` consequence. |
| BC2002 | Theorem 2.2 records the Erdos-Turan bridge and Weyl criterion; Theorem 3.3 repeats the conditional base-2 pi result. | General base for the deterministic bridges; pi-specific output only base 2. | The inequality is finite once sums are supplied, but no pi-specific sums or rates are supplied. Hypothesis 3.1 has no effective onset. | **Rejected:** the exact missing premise is a fixed-pi base-10 simultaneous exponential-sum estimate; Hypothesis 3.1 is unproved and base 2 only. |
| LAG2001 | Theorem 4.1: Strong Dichotomy Hypothesis implies a BBP-number is rational or normal to its BBP base. | Any BBP base `b`; pi's retained BBP formula is base 16. | Conditional qualitative asymptotics only; no discrepancy or prefix rate. | **Rejected:** Strong Dichotomy is an explicitly stated unmet hypothesis, and no transfer to base 10 or T3 rate is given. |
| BL2010 | Theorem 4.1 proves Property (P) implies base-`m` normality; Conjecture 4.1 asserts Property (P) for pi in every integer base. | Includes `m=10`; Property (P) has all-scale LDP quantifiers. | The pi premise is a conjecture. The proof is asymptotic and supplies no explicit word-length onset or `C*k*10^k` deadline. | **Rejected:** the quoted unmet hypothesis is Conjecture 4.1; even assuming ordinary normality alone would not instantiate T3's quantitative certificate. |
| SCH1960 | Theorem 1A transfers normality exactly when bases are multiplicatively dependent; Theorem 1B gives continuum many counterexamples when they are independent. | Arbitrary integer bases `r,s`; `16` and `10` are independent. | Existence theorem, not a fixed-pi result; no prefix rates. | **Rejected as transfer route:** base-16 normality does not generally imply base-10 normality, so a new pi-specific transfer theorem would be required. |
| BS2014 | Theorem 4 independently controls discrepancy rates in multiplicatively independent bases for constructed absolutely normal numbers. | Arbitrary fixed base `s` versus all bases independent of `s`; constructed numbers, not pi. | Computable constructions, but rates can be made arbitrarily different between bases. | **Rejected as transfer route:** confirms that even normality plus a rate in base 16 supplies no general base-10 rate; theorem has no pi hypothesis. |
| BBG2004 | Theorem 7 excludes Q-linear `b`-ary Machin-type BBP arctangent formulas for pi when `b>2` is not a proper power. | Includes base 10. | Effective formula-class exclusion; no digit-stream assertion. | **Rejected as positive route:** it rules out one decimal extraction mechanism and supplies no discrepancy, block occurrence, or T3 witnesses. It does not exclude every possible decimal BBP formula. |
| SGCF2025 | Theorem 1 and Corollary 1 claim high-probability binary occurrence with an explicit `N`. | Binary; one fixed word and probability `p`, under Hypotheses 1-2. | Explicit `N = n-1 + ceil(log(1-p)/log(1-2^-n))`; probabilistic and based on finite experiments. | **Rejected:** unsupported equiprobability/independence hypotheses, wrong base, no deterministic all-word assertion, and no T3 sums. Overlapping windows used in Equation (11) are not independent. |
| TRU2016 | Counts all words of lengths at most 3 in one fixed decimal and hexadecimal prefix. | Bases 10 and 16; only `k=1,2,3` and fixed finite prefix lengths. | Exact finite computation, no universal quantifier or asymptotic theorem. | **Rejected:** `experiment` only; no arbitrary `k`, uniform `C`, or Fourier certificate. |

No row instantiates T3.

## 3. Exact Quotations And Unmet Hypotheses

Line locators below refer to full `pdftotext -layout` output regenerated by
`./reproduce.sh fetch NEW_DIRECTORY`. The retained PDFs are authoritative.
Quotation words are transcribed from the source; line wrapping is normalized
and mathematical glyphs are rendered in ASCII where Markdown cannot preserve
the PDF encoding. Displayed omissions are marked by ellipses rather than
silently completed.

### BBP1997: extraction is not distribution

Theorem 1 states:

> "The following identity holds:"

and displays

```text
pi = sum_(i=0)^infinity 16^(-i)
  * (4/(8i+1) - 2/(8i+4) - 1/(8i+5) - 1/(8i+6)).
```

The abstract states:

> "We give algorithms for the computation of the d-th digit of certain
> transcendental numbers in various bases."

([BBP1997], report pp. 1 and 3; extracted lines 20-30 and 108-127.) The
quantifier is an input position `d`, not a guarantee that a specified value or
word ever occurs. Nothing in the theorem bounds the distribution of
`fract(10^j*pi)`.

### BC2001: conditional base 16/2 normality

The exact hypothesis is:

> "Hypothesis A. Denote by r_n = p(n)/q(n) a rational-polynomial function,
> i.e. p,q in Z[X]. Assume further that 0 <= deg p < deg q, with r_n
> nonsingular for positive integers n. Choose an integer b >= 2 and initialize
> x_0 = 0. Then the sequence ... determined by the iteration
> x_n = (b x_(n-1) + r_n) mod 1 either has a finite attractor or is
> equidistributed in [0,1)."

Its conditional result is:

> "Theorem 1.1. On Hypothesis A, each of the constants pi, log 2, zeta(3) is
> normal to base 2, and log 2 is also normal to base 3."

For the displayed base-16 pi iteration the authors say:

> "if it could be established that the iteration ... is equidistributed in
> [0,1), then it would follow that pi is normal to base 16 (and ... also
> normal to base 2)."

([BC2001], journal pp. 176-177; extracted lines 55-97.) "If it could be
established" is the specifically quoted unmet hypothesis. Theorem 2.4 further
states transfer only to integer bases `c=b^r`, and warns that numbers normal to
one base need not be normal to a base that is not a rational power
(extracted lines 239-248). Neither 10 nor any positive power of 10 is a power
of 16.

### BC2002: deterministic bridge, absent pi estimate

Theorem 2.2(9) says:

> "There exists an absolute constant C such that for any positive integer m
> the discrepancy of any sequence ... satisfies"

the displayed Erdos-Turan bound involving
`1/m + sum_(h=1)^m |N^(-1) sum_(n<N) exp(2*pi*i*h*alpha_n)|/h`.
Theorem 2.2(8) gives the Weyl criterion, and (12) says base-`b` normality is
equivalent to discrepancy tending to zero. ([BC2002], journal pp. 529-530;
extracted lines 192-252.) These are usable implications but not estimates for
pi.

The paper explicitly says:

> "It is unknown whether this hypothesis be true"

and then states:

> "Theorem 3.3. (Conditional.) On Hypothesis 3.1, each of the constants pi,
> log 2, zeta(3) is 2-normal."

([BC2002], journal p. 531; extracted lines 257-317.) T3 needs the missing
base-10 sums themselves, uniformly through a cutoff growing with `k`, plus a
prefix deadline. Neither the general inequality nor the conditional base-2
conclusion supplies them.

### LAG2001: the dichotomy remains a hypothesis

Lagarias states:

> "Strong Dichotomy Hypothesis ... the orbit ... either has finitely many
> limit points or is uniformly distributed on [0,1]."

Theorem 4.1 then says:

> "The Strong Dichotomy Hypothesis implies that theta is either rational or
> a normal number to base b."

([LAG2001], preprint pp. 9-10; extracted lines 490-543.) The theorem is
conditional, qualitative, and in the BBP base. It has neither a decimal
specialization for pi nor a discrepancy rate.

### BL2010: direct decimal route, conjectural pi premise

The exact implication is:

> "Theorem 4.1. Property (P) implies the normality of
> sum_(i>=1) D_i m^(-i) in basis m."

The exact fixed-pi premise is labeled:

> "Conjecture 4.1. For every integer m >= 2, the digits of the fractional part
> of either Pi or the Euler constant in basis m satisfy (P)."

([BL2010], preprint pp. 18-19; extracted lines 956-1009.) This includes base
10 but is a `conjecture`. The following paragraph says it is "supported by
numerical experiments" and uses 160 million decimal digits (lines 1009-1023),
which does not discharge the universal premise. Even a proof of ordinary
normality would not by itself give the `k`-uniform prefix rate required by T3.

### SCH1960 and BS2014: no general base transfer

Schmidt defines multiplicative dependence by coincidence of positive powers
and states:

> "THEOREM 1. A Assume r ~ s. Then any number normal to base r is normal to
> base s. B If r [is multiplicatively independent of] s, then the set of
> numbers xi which are normal to base r but not even simply normal to base s
> has the power of the continuum."

([SCH1960], printed p. 661; extracted lines 32-41. The extraction corrupts the
relation glyph; the rendered PDF is authoritative.) Since `16^a = 10^b` has
no positive integer solution, base 16 and base 10 are independent. This does
not say anything negative about pi; it refutes only an unrestricted transfer
principle.

Becher-Slaman strengthen the rate separation:

> "Theorem 4. Fix a base s. There is a computable function f ... decreasing
> to 0 such that for any function g ... decreasing to 0 there is an absolutely
> normal real number xi whose discrepancy for base s eventually dominates g
> and whose discrepancy for each base multiplicatively independent to s is
> eventually dominated by f."

([BS2014], preprint p. 3; extracted lines 139-147.) Thus even discrepancy rates
of an absolutely normal number need not transfer uniformly between independent
bases. A pi-specific theorem connecting the decimal orbit to the hexadecimal
one is an unmet hypothesis, not a standard base-change corollary.

### BBG2004: a restricted decimal BBP exclusion

The exact result is:

> "Theorem 7 Given b > 2 and not a proper power, there is no Q-linear b-ary
> Machin-type BBP arctangent formula for pi."

([BBG2004], printed p. 918; extracted lines 1161-1205.) Base 10 meets the
hypotheses, so this rigorously excludes that defined formula class. It neither
excludes every decimal random-access formula nor gives a digit-distribution
bound. In particular, an extraction formula would still require a separate
quantitative equidistribution theorem to reach T3.

### SGCF2025: explicit binary probability under unsupported assumptions

The paper's premises include:

> "Hypothesis 1. The probability of x_i being 0 or 1 is
> P(x_i=0)=P(x_i=1)=1/2."

and

> "Hypothesis 2. ... P(A_n intersection B_m) = P(A_n) times P(B_m)."

It then states:

> "Theorem 1. As the length N of the string A_N approaches infinity, the
> probability of the n-bit string A_n appearing at least once as a contiguous
> bit string within A_N tends to 1."

Corollary 1 gives

```text
N = n - 1 + ceil(log(1-p) / log(1-2^(-n))).
```

([SGCF2025], printed pp. 7-12; extracted lines 344-649.) The paper explicitly
bases Hypothesis 1 on 245 observed bits and Hypothesis 2 on finite statistical
tests. Moreover, its binomial Equation (11) treats all overlapping length-`n`
windows as independent (lines 551-589). This is false even for iid fair bits:
for the target `00`, adjacent-window joint probability is `1/8`, not
`(1/4)^2=1/16`. The result is therefore not a deterministic theorem about pi,
not decimal, not simultaneous over all words, and not a T3 certificate.

### TRU2016: finite computation only

The abstract and conclusion say:

> "The frequencies of all sequences up to length 3 in the first
> 22,459,157,718,361 decimal and 18,651,926,753,033 hexadecimal digits of pi
> are found to be consistent with the hypothesis of pi being a normal number
> in base 10 and base 16."

([TRU2016], preprint pp. 1 and 3; extracted lines 8-18 and 149-153.) The source
itself calls these "empirical consistency checks." Classification:
`experiment`. It proves only facts about a finite prefix and carries no
evidence for universal C1.

## 4. Exact Missing Hypotheses

Within this documented corpus, a successful T3 substitution would still need
all of the following, none of which is supplied by a retained theorem:

1. A theorem for the named input `pi`, not almost every real and not an
   artificial constructed number.
2. Base 10, or a new pi-specific theorem transferring quantitative
   distribution from base 2/16 to base 10.
3. One constant `C` uniform in every positive word length `k`.
4. For each `k`, an effective prefix `0 < N <= C*k*10^k`.
5. A common effective bound for every signed frequency `0 < |h| <= H`, with
   `H,B,N` satisfying T3's strict numerical inequality.
6. Deterministic conclusions about pi; neither confidence bounds nor finite
   digit tests discharge these quantifiers.

Ordinary base-10 normality would imply eventual occurrence of every fixed
word, but without a convergence modulus uniform in `k` it would still not
yield the canonical `C*k*10^k` deadline or instantiate T3.

## 5. Bounded Conclusion

For the ten primary sources, four prior audits, and four finite metadata
queries recorded in `retrieval_manifest.json`, no candidate instantiates T3.
The closest fixed-pi decimal premise is Barral-Loiseau's explicit Conjecture
4.1; the closest BBP route is Bailey-Crandall's unproved base-16 dynamical
dichotomy; the closest explicit block deadline is Silva-Garcia et al.'s
binary probabilistic formula under unsupported hypotheses. Schmidt and
Becher-Slaman show why no unrestricted base-16-to-base-10 normality or rate
transfer can fill the gap. BBP extraction and all retained finite digit counts
remain computational mechanisms or `experiment`, not evidence for C1.

This is a negative finding only for the documented corpus. It is not a claim
that no applicable theorem exists outside the searched bounds, and it does not
upgrade C1 from `open`.

## 6. Replay

From this artifact directory:

```sh
./reproduce.sh verify
./reproduce.sh fetch /tmp/t4-replay
```

`verify` checks every retained artifact and pinned local dependency. `fetch`
requires a new output path, downloads every primary PDF, verifies its SHA-256,
runs `pdftotext -layout`, verifies each extraction hash, and replays the four
mutable search queries. A changed future publisher payload is reported as a
source-version change; it does not alter the retained evidence pin.
