# Factor-complexity applicability matrix for pi

Status: **literature-checked** on 2026-07-21 for the pinned sources in
`SOURCE_MANIFEST.md`.  This is not an exhaustive proof that no other theorem
exists.  It is a source-pinned test of the named routes in agenda item T2.

## Canonical target and verdict policy

The immutable canonical statement has SHA-256
`e2b6c9375936a97fe6cdd10c3f014613267f3c491935b536c6ec016c5f501e43`.
For the fractional decimal digit stream of pi, `p_pi(n)` counts distinct
contiguous length-`n` blocks beginning at arbitrary positions.  The target A1
is

> for every real `C > 0`, there is `N >= 1` such that for every `n >= N`,
> `p_pi(n) > C n`.

Equivalently, `p_pi(n)/n -> infinity`.  The recorded siblings used below are:

- A2: `p_pi(n) - n -> infinity` (strictly weaker than A1).
- A4: `p_pi(n) >= n + 1` for every `n >= 1` (linear baseline).
- A5: `p_pi(n) = 10^n` for every `n >= 1` (disjunctivity endpoint).

Verdicts have a deliberately narrow meaning:

- **YES**: every hypothesis has been matched for the canonical decimal stream.
- **NO**: a hypothesis is false, the theorem is about a different object/base,
  or the conclusion cannot establish the claimed canonical consequence.
- **NOT KNOWN**: an indispensable hypothesis is not known for pi.

A **YES** can still yield only A4; it is not automatically progress on A1.

## Summary matrix

| ID | Source result | Literal conclusion | Applicability to canonical decimal pi | Consequence for A1 |
|---|---|---|---|---|
| MH-1 | Morse--Hedlund 1938, Theorem 7.4 | A nonperiodic two-sided trajectory using `mu` symbols has `P(n) >= n + mu - 1` | **NO**: the source theorem is stated for a two-sided trajectory, while the canonical object is a one-sided stream | None directly; it is the historical two-sided baseline |
| AB-1 | Adamczewski--Bugeaud 2007, Theorem 1 | Every irrational algebraic real has `liminf p(n)/n = infinity` in every integer base | **NO**: pi is transcendental, hence not algebraic | The conclusion would be exactly A1, but its algebraicity hypothesis is false for pi |
| AB-2 | Adamczewski--Bugeaud 2007, Theorem 2 | An irrational algebraic number cannot have an automatic base-`b` expansion | **NO**: pi is not algebraic; automaticity is also not a verified property of its decimal expansion | No quantitative lower bound for pi |
| LC-1 | Adamczewski--Bugeaud 2007, Theorem 3 plus Fibonacci-word example | The explicitly constructed Fibonacci/Sturmian binary number is transcendental while `p(n)=n+1` | **NO**: constructed binary number, not pi's decimal stream | Demonstrates that transcendence alone does not imply A1 |
| LC-2 | Adamczewski--Bugeaud 2007, Theorem 1 plus Kempner automatic example | The explicitly constructed Kempner binary number is transcendental and has `p(n)=O(n)` | **NO**: constructed binary number, not pi's decimal stream | A second linear-complexity transcendental construction; no transfer to pi |
| LC-3 | Adamczewski--Bugeaud 2007, consequence of Theorem 1 | An irrational real with `p(n)=O(n)` is transcendental | **NOT KNOWN** as a hypothesis for pi; the implication cannot be reversed from pi's transcendence | No A1 consequence; using the converse would be invalid |
| PI-1 | Bailey--Crandall 2001, Hypothesis A and Theorem 1.1 | Hypothesis A implies that pi is normal to base 2; a specified equidistribution instance implies base-16 normality | **NO** for the canonical decimal target; the hypothesis is **NOT KNOWN**, and bases 2/16 are not base 10 | No decimal complexity conclusion |
| PI-2 | Base-10 normality implication from Bailey--Crandall Definition 2.1 | If pi is normal to base 10, then every decimal block occurs and `p_pi(n)=10^n` | **NOT KNOWN**: base-10 normality of pi is unproved in the pinned sources | Would prove A5 and hence A1, but no hypothesis match exists |
| PI-3 | Trueb 2016 finite digit-frequency study | Length-1, 2, and 3 frequencies in a finite prefix are statistically consistent with normality | **NO** as a theorem application: finite experiment only | No asymptotic conclusion; not evidence for any universal quantifier |

## Row-by-row hypothesis audit

### MH-1: original two-sided theorem

**Pinned source.** S1, Theorem 7.4, p. 830.  The scan reads: if `t` is a
nonperiodic trajectory involving `mu` generating symbols, then
`P(n) >= n + mu - 1`.  Theorem 7.3 and its corollary on pp. 829--830 say
that equality `P(m+1)=P(m)` forces a period and hence a nonperiodic trajectory
has strictly increasing complexity.

**Hypotheses and matches.**

| Hypothesis | Status for canonical pi | Evidence |
|---|---|---|
| `t` is a trajectory indexed in both directions | **NO** | S1 distinguishes trajectories from rays; the canonical stream is indexed only by positive fractional positions |
| Symbols come from a finite set | **YES** | Canonical alphabet is `{0,...,9}` |
| The trajectory is nonperiodic | **NOT A LITERAL MATCH** | Pi's one-sided stream is not eventually periodic, but it is not itself S1's two-sided trajectory |
| `P(n)` counts all contiguous factors | **YES for the analogous notion** | S1 p. 829 defines `P(n)` as the number of different `n`-blocks; canonical factors use the same contiguous-block convention |

**Verdict: NO (direct application).**  Reporting S1 alone as a theorem about
the one-sided decimal stream would suppress a domain hypothesis.  The exact
one-sided bridge is recorded separately below because it is machine-checked
local support, not another primary-literature matrix row.

### Separate machine-checked support: exact one-sided baseline

**Pinned result.** The accepted T1 artifact (hash in `SOURCE_MANIFEST.md`),
`DecimalFactorComplexity.morse_hedlund_canonical`, is the exact one-sided
counterpart: a finite-alphabet stream that is not eventually periodic has
canonical factor complexity at least `n+1` for every positive `n`.  S1 is the
historical primary source; S4 supplies the pi-specific irrationality input.

**Hypotheses and matches.**

| Hypothesis | Status for canonical pi | Evidence |
|---|---|---|
| One-sided stream | **YES** | Canonical digits are `d_1,d_2,...` |
| Finite alphabet with decidable equality | **YES** | Ten decimal digits |
| Factors are contiguous and may start anywhere | **YES** | T1 definitions `OccursAt`, `factorSet`, and `canonicalFactorComplexity` match the canonical statement |
| Stream is not eventually periodic | **YES** | S4 proves pi irrational.  An eventually periodic base-10 expansion is a finite prefix plus a geometric series and is rational; contraposition applies |

**Applicability verdict: YES, but only A4.**  It proves
`p_pi(n) >= n+1`, not A1, A2, or A5.  This is not counted as a literature
matrix row: its evidence is the separately pinned and recompiled Lean artifact.

### AB-1: algebraic irrational superlinear complexity

**Pinned source.** S2, Theorem 1, pp. 549--550.  S2 defines `p(n)` on
p. 549 as the number of distinct length-`n` digit blocks and proves
`liminf_{n->infinity} p(n)/n = infinity` for every irrational algebraic
number in every integer base `b >= 2`.

**Hypotheses and matches.**

| Hypothesis | Status for pi | Evidence |
|---|---|---|
| `b` is an integer and `b >= 2` | **YES** | Choose `b=10` |
| The word is the base-`b` digit expansion | **YES** | Canonical word is pi's base-10 fractional expansion |
| Factors are all contiguous blocks, not prefixes only | **YES** | S2 p. 549 and canonical statement use the same definition |
| The represented real is irrational | **YES** | S4, p. 509 |
| The represented real is algebraic | **NO** | S5 proves pi is not algebraic (pi is transcendental) |

**Verdict: NO.**  The conclusion is the exact A1 asymptotic, but the central
algebraicity hypothesis is false for pi.  Transcendence is not a stronger
hypothesis here; it places pi outside the theorem's domain.

### AB-2: automatic expansions of algebraic irrationals

**Pinned source.** S2, Theorem 2, p. 550: an irrational algebraic number's
base-`b` expansion cannot be generated by a finite automaton.

**Hypotheses and matches.**

| Hypothesis | Status for pi | Evidence |
|---|---|---|
| Integer base `b >= 2` | **YES** | Choose `b=10` |
| Irrational | **YES** | S4 |
| Algebraic | **NO** | S5 |

**Verdict: NO.**  The theorem neither applies to pi nor states a quantitative
factor-complexity lower bound for transcendental numbers.  Whether pi's decimal
expansion is automatic is not a hypothesis of Theorem 2; it is a separate
unknown property, and Theorem 2 cannot be contraposed from transcendence.

### LC-1: a transcendental number of minimal complexity

**Pinned source.** S2, pp. 552--553, defines the Fibonacci morphism
`0 -> 01`, `1 -> 0`, gives its fixed word, and states that this word is
Sturmian with `p(n)=n+1` for every positive `n`.  Theorem 3 on p. 550 says
that a binary algebraic irrational cannot be generated by a morphism.  The
Fibonacci word is non-eventually-periodic (its unbounded complexity rules out
eventual periodicity), so its binary real is irrational; Theorem 3 therefore
makes that real transcendental.

**Hypotheses and matches.**

| Hypothesis/object identity | Status for pi | Evidence |
|---|---|---|
| Binary expansion is the Fibonacci morphic fixed word | **NO** | This defines a particular constructed real, not pi's decimal expansion |
| Base is 2 | **NO for canonical target** | Canonical target is base 10 |
| Word is non-eventually-periodic/irrational | **YES for the construction** | `p(n)=n+1` is unbounded, unlike an eventually periodic word |
| Word is generated by a binary morphism | **YES for the construction** | Explicit morphism on S2 pp. 552--553 |

**Verdict: NO for pi.**  This row is a counterexample to the inference
"transcendental number implies superlinear factor complexity": the constructed
number is transcendental and has exactly the Morse--Hedlund minimum `n+1`.

### LC-2: the Kempner automatic number

**Pinned source.** S2 p. 553 gives the classical binary automatic number
`xi_K = sum_{n>=1} 2^(-2^n)`.  S2 p. 550 records that every automatic
sequence has `p(n)=O(n)`.  The gaps between successive `1` digits of `xi_K`
are unbounded, so its expansion is not eventually periodic and `xi_K` is
irrational.  S2 Theorem 1 then proves it cannot be algebraic; hence it is
transcendental.  (S2 also cites Kempner's original transcendence proof, but
the inference just given uses S2's own theorem.)

**Hypotheses and matches.**

| Hypothesis/object identity | Status for pi | Evidence |
|---|---|---|
| Binary expansion has `1` exactly at positions `2^n` | **NO** | This defines `xi_K`, not pi's decimal expansion |
| Expansion is automatic | **YES for the construction** | S2 p. 553 explicitly calls `xi_K` binary automatic |
| Factor complexity is `O(n)` | **YES for the construction** | S2 p. 550 states this for every automatic sequence |
| Expansion is not eventually periodic | **YES for the construction** | Successive gaps between `1` digits are unbounded |

**Verdict: NO for pi.**  Together with LC-1, this supplies a second explicit
transcendental construction of linear factor complexity.  Neither construction
provides a theorem transferring low or high complexity to pi.

### LC-3: low complexity as a sufficient condition for transcendence

**Pinned source.** Immediately after S2 Theorem 1 on p. 550, the authors
deduce that every irrational real with `p(n)=O(n)` is transcendental.

**Hypotheses and matches.**

| Hypothesis | Status for pi | Evidence |
|---|---|---|
| Irrational real | **YES** | S4 |
| Fixed integer-base expansion | **YES** | Choose decimal base 10 |
| `p_pi(n)=O(n)` | **NOT KNOWN** | This is incompatible with A1 and is not established by any pinned source |

**Verdict: NOT KNOWN as an applicability hypothesis, with no A1 payoff.**
Even if the low-complexity hypothesis were proved, the conclusion would only
reprove the already known transcendence of pi.  Applying the converse
"transcendental implies low complexity" would be a logical error, and LC-1
and LC-2 show that transcendental numbers can occupy the linear-complexity
regime.

### PI-1: conditional binary/hexadecimal normality

**Pinned source.** S3, Hypothesis A and Theorem 1.1, local PDF pp. 2--3.  Hypothesis
A concerns every recurrence
`x_n = (b*x_{n-1} + p(n)/q(n)) mod 1` with integer polynomials,
`0 <= deg p < deg q`, no positive-integer pole, integer `b>=2`, and
`x_0=0`: it asserts that the orbit either has a finite attractor or is
equidistributed.  Theorem 1.1 says that Hypothesis A implies pi is normal to
base 2.  S3 local PDF pp. 3 and 11 also gives a particular base-16 recurrence whose
equidistribution would imply pi normal to base 16 (and hence base 2).

**Hypotheses and matches.**

| Hypothesis | Status for pi | Evidence |
|---|---|---|
| Hypothesis A | **NOT KNOWN** | S3 explicitly labels it a hypothesis and says even one relevant instance would have remarkable consequences (local PDF p. 3) |
| Required generalized-polylogarithm series for pi | **YES** | S3 proof of Theorem 1.1, local PDF p. 10, points to equations (7)--(9) |
| Pi irrational | **YES** | S4; also used explicitly in S3's proof |
| Conclusion concerns base 10 | **NO** | Theorem 1.1 gives base 2; the specified recurrence gives base 16, and S3 Theorem 2.4 transfers only among rational powers of a base, not from 2/16 to 10 |

**Verdict: NO for canonical decimal applicability.**  There are two independent
blockers: the dynamical hypothesis is not known, and the theorem's conclusion
is in the wrong base.  It must not be reported as a theorem that pi is normal
in any base.

### PI-2: the decimal-normality endpoint

**Pinned source.** S3 Definition 2.1, local PDF p. 4, defines normality to base
`b` by positive limiting frequency `b^{-n}` for every length-`n` string.
Consequently, base-10 normality of pi would make all `10^n` decimal words
occur, so `p_pi(n)=10^n` (A5).  S6 p. 1 says a proof of pi normality is
lacking and performs only an empirical check; S3 local PDF p. 2 likewise identifies
normality of pi as open at its publication date.

**Hypotheses and matches.**

| Hypothesis | Status for pi | Evidence |
|---|---|---|
| Pi is normal to base 10 | **NOT KNOWN** | S6 p. 1: "a proof is still lacking"; S3 local PDF p. 2 gives the same status in 2001 |
| Canonical factors are contiguous arbitrary-position decimal blocks | **YES** | This is exactly what positive block frequencies quantify |

**Verdict: NOT KNOWN.**  If the missing normality hypothesis were proved, this
would establish A5 and therefore A1.  No pinned theorem supplies that
hypothesis.

### PI-3: finite decimal digit statistics

**Pinned source.** S6 reports frequencies for all words of lengths 1, 2, and
3 among the first `22,459,157,718,361` decimal digits and the first
`18,651,926,753,033` hexadecimal digits.  Its Table 1 and conclusion say the
observations are statistically consistent with normality.  This audit could
not rerun that experiment: the PDF and its linked record page identify
y-cruncher, formulas, hardware, and run duration, but do not provide the full
digit dataset, the frequency-analysis code and exact command, or raw counts for
all words.  The arXiv e-print endpoint serves the same PDF rather than a source
package containing reproducibility material.

**Hypotheses and scope.**

| Requirement for A1 | Status of S6 evidence | Evidence |
|---|---|---|
| All sufficiently large lengths `n` | **NO** | Only `n=1,2,3` are tested |
| Infinite digit stream | **NO** | A finite prefix is tested |
| Deterministic proof rather than a statistical model | **NO** | Expected bands assume binomially distributed occurrences |
| Exact lower bound for `p_pi(n)` | **NO** | Frequencies are measured; no asymptotic factor-complexity theorem is proved |
| Independent reproduction in this audit | **NO** | Missing analysis code, exact command, raw counts, and 22.4-trillion-digit dataset |

**Verdict: NO.**  Label: **source-reported experiment, not independently
reproduced**.  The report cannot establish A1, A2, A4, A5, normality, or any
universal statement, and this audit does not promote its numerical claims to
independently verified evidence.

## Literature search record and limitation

The following searches were run on 2026-07-21 to look for a pi-specific
factor-complexity or digit-distribution theorem before selecting the pinned
rows:

- Crossref title/keyword queries for `pi digit expansion irrationality
  measure`, `Symbolic Dynamics Morse Hedlund`, and the exact titles of S2 and
  S3.
- arXiv API queries for `pi AND digit AND complexity` and `pi AND normality`.
- OpenAlex DOI records for S1 and the low-complexity literature.

The arXiv normality query located S6 and other empirical/conjectural papers;
the targeted `pi AND digit AND complexity` query returned no relevant
factor-complexity theorem among its 14 results.  Database nonappearance is not
proof of nonexistence, so this matrix does **not** assert a globally exhaustive
negative literature result.  It asserts only the row-level verdicts above.

## Decision for goal G2

Within this pinned matrix, **no theorem with all hypotheses verified for pi
improves the linear A4 baseline for its decimal factor complexity**.

- The only source conclusion exactly matching A1 is S2 Theorem 1, whose
  algebraicity hypothesis is false for pi.
- Known transcendental low-complexity examples show that transcendence cannot
  replace algebraicity in that theorem.
- The pi-specific theorem is conditional and concerns bases 2/16, while the
  decimal evidence is finite computation.
- Decimal normality would solve the stronger A5 endpoint, but its hypothesis
  is not known.

Thus this detour should be parked unless a future source provides a genuinely
pi-specific decimal hypothesis stronger than irrationality.  This is a
**literature-checked negative route assessment**, not a proof that A1 is false
and not a claim of exhaustive novelty.
