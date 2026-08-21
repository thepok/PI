# T5: bounded applicability audit for decimal pi lower block density

Status: `literature-checked` on 2026-07-22 for exactly the six-source,
eleven-row corpus frozen in `CORPUS.json`. This is not an exhaustive search and
does not prove or disprove C1. No finite computation of pi digits is used.

## 1. Immutable target and quantifiers

The canonical statement is
`knowledge/pi/statements/pi-positive-lower-block-density.txt`, SHA-256
`11ec455612e8ab182b7f6c71ba1a64c3b5b30beb5f3ded632cb2ecdc50129cc8`.
It asks whether

```text
for every integer k >= 1,
for every w in {0,...,9}^k, including leading-zero words,
liminf_(N->infinity) A_pi(w,N)/N > 0.                 (C1)
```

Here `A_pi(w,N)` counts every overlapping start `0 <= n < N` in the fixed
nonterminating decimal expansion of pi. It is not a first-occurrence,
positive-upper-density, other-base, logarithmic-density, or almost-everywhere
question.

The exact comparison target is accepted T3,
`knowledge_library/t3/T3FiniteFourierLowerDensity.lean`, SHA-256
`50f169aef3efd7d940cefd1447673fc3f828db9317251dda86b5d563e631befa`.
For every fixed `k >= 1`, the literature would instantiate T3 if it supplied
`H,N0 : Nat` and `epsilon,eta : Real` such that

```text
1 <= N0, 0 <= epsilon, 0 < eta,
eta <= (1 - H*epsilon - 10^(2*k)/(H+1))/(H+1),
```

and, for every `N >= N0` and every integer `h` with
`h != 0` and `|h| <= H`, supplied the fixed-pi estimate

```text
|sum_(j=0)^(N-1) exp(2*pi*i*h*fract(10^j*pi))| <= epsilon*N.   (T3-SUM)
```

One `N0` must work for every later `N` and every signed frequency in the
finite cutoff. The witnesses may depend on `k`. T3 then gives one positive
lower bound `eta` for every length-`k` word and every `N >= N0`. To prove C1
through T3, this must be done for every `k`.

### Ambiguous quantifiers fixed before comparison

1. "Almost every x" cannot be specialized to the named point `x=pi`.
2. A base-2 or base-16 theorem is not a decimal theorem. No unrestricted
   transfer exists between the multiplicatively independent bases 16 and 10.
3. A finite computation verifies only a finite prefix and is never a C1 or
   T3 proof.
4. Dense or digit-dense means every cylinder is hit, but does not imply
   positive lower visit frequency.
5. Uniform distribution or base-10 normality would be stronger than C1, but
   a theorem giving only a criterion for it does not verify the criterion at
   pi.
6. An ineffective threshold is acceptable for T3 because `N0` is
   existential. The fixed-point and base requirements are not negotiable.
7. Bailey-Crandall's contained-prefix convention omits at most `k-1` starts
   relative to `A_pi(w,N)`. Dividing by `N` makes this finite boundary
   difference vanish, so a source limit `10^(-k)` compares exactly with C1.

## 2. Frozen corpus and source pins

The required core consists of Bailey-Crandall (2001), Lagarias (2001), and
the two named standard uniform-distribution references Weyl (1916) and
Kuipers-Niederreiter (1974). The only additions are Philipp (1975) and
Fukuyama (2008), each found in a retained bounded T5 title search and then
interpreted using accepted T28's locked theorem checks. Thus there are two
additional primary sources, below the cap of six. The eleven result rows are
below the cap of sixteen.

| ID | Retained source | Exact byte pin | Principal locators used |
|---|---|---|---|
| BC2001 | `sources/bailey-crandall-2001.pdf` | `701067697e8c1dace60cd8695ef509edae31f9da3bffd64b548624ccc2e4cfa8` | Hypothesis A and Theorem 1.1, retained author PDF pp. 2-3; Definition 2.1, p. 4; Theorem 2.2, p. 5; Theorem 2.4, p. 6; decimal BBP discussion, p. 16 |
| LAG2001 | `sources/lagarias-2001.pdf` | `a2a1171eb9c75c9fa3495ca3c3ceaa33c1d20b722bb56f82adb56d8c308209b9` | Theorem 2.1, preprint p. 5 / journal pp. 358-359; Strong Dichotomy and Theorem 4.1, preprint pp. 9-10 / journal pp. 361-362 |
| WEYL1916 | `sources/weyl-1916.pdf` | `6c5d8e384f62ea01cd4b0240ed48246324880d991cd14299ff260dd4ca7e4531` | Section 1, equation (2) and Satz 1, printed pp. 313-315 |
| KN1974 | `sources/kuipers-niederreiter-1974.pdf` | `b52cc1f9a3fa41489d6cb09897608e80644319a3de4a77c284a3671117068b98` | Ch. 1, Sec. 2, Theorem 2.1, p. 7; Ch. 2, Sec. 2, Theorem 2.5, equation (2.33), p. 112 |
| PH1975 | `sources/philipp-1975.pdf` | `4d0edc8170fe1ddf368ada0fd64ed7ec48411840ab6c07fdd658e44fbae84e3a` | Theorem 1, pp. 241-242; deterministic inequality (3.9) and note added, p. 250 |
| FU2008 | `sources/fukuyama-2008.pdf` | `59b263e7d74aa627606181646c75c02803c41d42af4d1780f7ff8de28f917266` | Main Theorem and Corollary, manuscript pp. 1-2 / journal pp. 155-156 |

The DOI, retrieval URL, byte count, extraction method, and extraction hash
where meaningful are recorded in `CORPUS.json`. `reproduce.sh verify`
regenerates the six `pdftotext -layout` outputs in a temporary directory and
checks those extraction hashes. Weyl and Philipp are image scans. Weyl
printed p. 315 was rendered and OCRed only as an approximate working aid; the
retained scan was visually checked for `Satz 1` and its displayed `o(n)`
formula. The temporary render and OCR are not retained evidence. Philipp's
exact scan checks are imported from locked T28 and were not repeated. The
PDFs, not OCR, are authoritative.

## 3. Verdict policy

- **YES**: the cited result, with all premises verified, proves the exact
  target for fixed decimal pi.
- **CONDITIONAL**: a deterministic source-defined route reaches the exact
  target after the recorded unproved fixed-pi premise, with no remaining base
  or quantifier mismatch.
- **NO**: an indispensable point, base, scope, or conclusion mismatch remains.

`NO` never means the target is false. Every negative conclusion below is
limited to this frozen corpus.

## 4. Row-by-row matrix

`CORPUS.json` is the normative full matrix: every row there has separate C1
and T3 verdicts, first unmatched premises, and exact comparison text. This
table is its human-readable index.

| Row and locator | Exact scope, base, and conditional status | C1 | T3 | First obstruction(s) |
|---|---|---|---|---|
| BC-A: Hypothesis A and Theorem 1.1, retained PDF pp. 2-3 | Rational-polynomial perturbed base-`b` maps; fixed-pi conclusion is conditional and base 16/2 | **NO** | **NO** | Hypothesis A is unproved; even granting it, the pi orbit is not base 10. |
| BC-ORBIT: Definition 2.1, retained PDF p. 4; Theorem 2.2, p. 5 | Every real and integer base; normality iff the base-power orbit is equidistributed | **CONDITIONAL** | **CONDITIONAL** | Base-10 equidistribution/normality of fixed pi is the unproved premise. |
| BC-TRANSFER: Theorem 2.4, retained PDF p. 6 | Normality transfers only between bases related by rational powers | **NO** | **NO** | No nonzero rational `r` has `10=16^r`; no decimal-orbit transfer results. |
| LAG-ORBIT: Theorem 2.1, preprint p. 5 | Every integer base; density iff digit-density, uniform distribution iff normality | **CONDITIONAL** | **CONDITIONAL** | The fixed decimal pi orbit is not known uniformly distributed. Density alone would still be too weak for C1. |
| LAG-DICHOTOMY: Strong Dichotomy and Theorem 4.1, preprint pp. 9-10 | Every BBP number satisfying the degree condition, conditional in its BBP base | **NO** | **NO** | Strong Dichotomy is unproved and the known pi BBP base is 16, not 10. |
| WEYL-CRITERION: equation (2) and Satz 1, pp. 313-315 | Every real sequence; normalized sums vanish for every nonzero integer frequency iff the sequence is uniformly distributed | **CONDITIONAL** | **CONDITIONAL** | The criterion's sums are unproved for the fixed sequence `fract(10^j*pi)`. |
| KN-WEYL: Ch. 1, Theorem 2.1, p. 7 | Modern base-neutral iff Weyl criterion | **CONDITIONAL** | **CONDITIONAL** | Same fixed-pi cancellation premise; the theorem tests it but does not prove it. |
| KN-ERDOS-TURAN: Ch. 2, Theorem 2.5, p. 112 | Every finite real sequence and cutoff; explicit discrepancy upper bound from finite sums | **CONDITIONAL** | **NO** | It gives a route from small sums to C1 but supplies no pi sum bound and therefore does not prove T3 itself. |
| PH-LIL: Theorem 1, pp. 241-242 | Every Hadamard-gap integer sequence, but only for almost every initial point; set `n_j=10^(j-1)` | **NO** | **NO** | The conull set is not known to contain pi. |
| PH-DETERMINISTIC: inequality (3.9), p. 250 | Every finite sequence; `|sum e(x_j)| <= 4*N*D_N` using the note-added constant | **CONDITIONAL** | **CONDITIONAL** | No theorem supplies the required fixed-pi discrepancies `D_N({h*10^j*pi}) -> 0`. |
| FU-GEOMETRIC: Theorem and Corollary, pp. 155-156 | Exact discrepancy LIL for `theta=10`, but only for almost every `x`; `Sigma_10=sqrt(220)/27` | **NO** | **NO** | Exact base 10 does not repair the almost-everywhere-to-fixed-pi gap. |

There is no YES row for either target.

## 5. Exact conditional match from uniform distribution to T3

The criterion rows are marked `CONDITIONAL`, rather than merely suggestive,
because their quantifiers can be matched exactly after the one stated
fixed-pi premise.

Fix `k >= 1` and assume Weyl cancellation for the decimal pi orbit at every
nonzero integer frequency. Choose

```text
H = 10^(2*k),
delta = 1 - 10^(2*k)/(H+1) > 0,
epsilon = delta/(2*H),
eta = delta/(2*(H+1)) > 0.
```

Then

```text
eta = (1 - H*epsilon - 10^(2*k)/(H+1))/(H+1).
```

For each of the finitely many integers `h` with `0 < |h| <= H`, normalized
sum convergence gives a threshold after which `|S_N(h,pi)| <= epsilon*N`
for every later `N`. The maximum of these finitely many thresholds is one
`N0`, exactly in T3's order. No effective value is needed. T3's accepted
formal theorem then yields eventual frequency at least `eta` for every
length-`k` word.

This paragraph is a conditional comparison, not evidence that pi satisfies
Weyl cancellation. The metric Philipp and Fukuyama rows establish analogous
behavior only for almost every initial point and therefore are not fixed-pi
proofs.

## 6. Locked evidence, not repeated audits

`LOCKED_EVIDENCE.md` identifies accepted content-addressed T28, T4, T9, and
T11 audits, their manifests, and their `verdict: done` evidence. T5 only uses
their established source pins and separation findings:

- T28: the first obstruction in the retained lacunary theorems is the
  almost-everywhere initial point;
- quantitative-block-hitting T4: Bailey-Crandall and Lagarias do not supply a
  fixed-pi decimal result, and finite digit computations are experiments;
- quantitative-block-hitting T9: deterministic irrationality and orbit-range
  results do not supply exponential-sum cancellation;
- decimal-factor-complexity T11: weighted metric and mean-square theorems
  remain non-pointwise at pi.

No prior replay script, metadata query, or theorem audit was executed for
this item. `reproduce.sh verify` only hashes the locked files.

## 7. Bounded conclusion

For the six sources and eleven rows frozen here, no cited theorem proves C1
or T3 for the fixed decimal expansion of pi. The closest exact routes are the
Weyl/orbit equivalences and Philipp's deterministic discrepancy-to-sum
inequality; all require an unproved fixed-pi decimal distribution premise.
The strongest direct base-10 lacunary discrepancy rows are almost-everywhere
theorems and cannot be labeled as pi results. The Bailey-Crandall and Lagarias
pi routes are additionally conditional and tied to base 16/2.

This is a negative applicability finding only for the frozen corpus. It is
not a global nonexistence claim, does not change C1 from `open`, and does not
promote any finite computation or almost-everywhere theorem to a fixed-pi
proof.

## 8. Replay

From this directory run:

```sh
./reproduce.sh verify
```

The command verifies the retained source/search/audit hashes, the immutable
canonical statement, the accepted T3 source, and all locked prior-audit
hashes. It also checks the corpus caps, required sources, row fields, and
verdict vocabulary. It is offline and does not rerun prior audits or mutable
literature searches.
