# T9: Deterministic Decimal-Orbit Audit Beyond T4

Status: `literature-checked` on 2026-07-22 for the bounded corpus and exact
retrievals in `retrieval_manifest.json`. This is not an exhaustive literature
claim, does not prove or disprove C1, and does not promote C1 from `open`.

## 1. Provenance And Normalized Target

The immutable statement is
`knowledge/pi/statements/pi-quantitative-block-hitting.txt`, SHA-256
`ab000220813f99eb40cfdc2d7fdae4ea7796291852df43dce7e6bf317c247449`.
It asks whether one integer `C >= 1` works simultaneously for every integer
`k >= 1` and every one of the `10^k` decimal words, including words beginning
with zero, so that an occurrence is fully contained in the first
`C*k*10^k` fractional digits of pi.

Equivalently, the orbit point `{10^n*pi}` must enter every half-open decimal
cylinder

```text
[a/10^k, (a+1)/10^k),  0 <= a < 10^k,
```

at a start `n` whose final length-`k` word remains inside the deadline. The
target scale is therefore exactly `10^(-k)`. This audit concerns the canonical
variant A1 only. It does not replace full containment by a start bound without
recording T3's explicit `C -> C+1` loss.

The comparison target is accepted T3,
`UniformPiAnalyticCover.lean`, SHA-256
`473277f59fd2735f70c8ad03c26c0c7c024c1fd611a1375ab4afdba35d3cc2cc`.
At each positive `k`, T3 asks for `N,H : Nat` and `B : Real` such that

```text
0 < N,
N <= C*k*10^k,
|sum_(j<N) exp(2*pi*i*h*fract(10^j*pi))| <= B
  for every integer h != 0 with |h| <= H,
H*B + N*10^(2*k)/(H+1) < N.
```

One `C` is uniform in `k`; `N,H,B` may depend on `k`.

### Ambiguous quantifiers resolved

- "Known for pi" means a theorem naming pi, with a pinned source. It does not
  mean numerical evidence from a finite prefix.
- "Deterministic" means the conclusion applies to the named input, not merely
  almost every input or a random input.
- A theorem about all times `n >= 0` but only one constant-size interval does
  not silently become a shrinking-target theorem.
- A theorem for multiplier `p/q` with `q >= 2` does not silently specialize to
  multiplier `10`, which has `q=1` in lowest terms.

## 2. Bounded Search And Exclusions

The corpus consists of four finite metadata queries retained byte-for-byte,
citation-chain screening from the 2024 Aistleitner--Berkes--Tichy survey, and
the primary papers retained in `sources/`. The API bounds are 30 Crossref
records for each of two subject queries, 30 OpenAlex records, and 20 Crossref
records for the pi query. Search URLs, response hashes, and source hashes are
in `retrieval_manifest.json`.

All ten T4 primary sources and T4's already screened Erdos--Gal, Philipp, and
Fukuyama metric theorems are excluded rather than duplicated. General
almost-everywhere shrinking-target, discrepancy, normality, and lacunary-sum
theorems are excluded. No finite digit computation is used anywhere in this
audit.

The survey makes the reason for the metric exclusion explicit. It states:

> "for other parametric sequences of the form ({n_k alpha}) ... in general it
> is completely impossible to determine whether for some particular value of
> alpha the sequence is u.d. or not."

It then states Weyl's result only as:

> "For every sequence of distinct integers (n_k), the sequence ({n_k alpha})
> is u.d. mod 1 for (Lebesgue-) almost all reals alpha."

([ABT2024], survey p. 5; extracted lines 209-229.) This theorem is not applied
to pi. The same survey describes proving normality of natural constants such
as pi in a fixed base as "completely hopeless" with current machinery and
notes that even the optimal discrepancy order for constructed normal numbers
is open ([ABT2024], pp. 20-22; lines 1053-1082). These are literature-map
statements, not negative theorems about pi.

Three retrieved citation-chain papers were screened out because their formal
hypothesis is `p > q >= 2`, and thus excludes integer base 10: Flatto--Lagarias--
Pollington (1995), Bugeaud (2004), and Dubickas (2009). Their DOI records and
exact exclusion reasons are in the manifest. Stefanescu's 2024 dispersion
paper was excluded because the available conclusions choose a dilation factor
or hold for Lebesgue-almost all factors, not for the fixed factor pi.

## 3. The Exact T3 Scale Before Comparing Sources

For `k >= 1`, T3's strict inequality itself imposes necessary scales. The case
`H=0` is impossible because its second term is `N*10^(2*k) >= 100*N`. Hence
`H >= 1`; the frequency bound then forces `B >= 0`. Dropping each nonnegative
term in turn gives

```text
N*10^(2*k)/(H+1) < N,       so H+1 > 10^(2*k), hence H >= 10^(2*k),
H*B < N,                    so B < N/H.
```

With `N <= C*k*10^k`, every T3 instantiation therefore necessarily satisfies

```text
H >= 10^(2*k),
B < C*k*10^(-k),
```

uniformly for every signed frequency `0 < |h| <= H`. Thus a qualitative
density statement, a constant lower bound on orbit diameter, or a pointwise
Diophantine lower bound does not approach the actual certificate: T3 needs a
simultaneous *upper* bound on unnormalized exponential sums at frequencies
through the square of the reciprocal target scale.

## 4. Candidate Matrix

| ID | Exact deterministic input/output | What is verified for pi | T3 substitution or exact obstruction |
|---|---|---|---|
| SAL2008 | Theorem 1 gives a uniform lower bound for rational approximation to pi with exponent `7.6063...`. | This is a fixed-pi theorem and in particular proves a finite irrationality measure. | It gives lower bounds on individual distances `||q*pi||`, not upper bounds on sums over `{10^j*pi}`. It supplies no `B`, and therefore cannot meet `H >= 10^(2k)` and `B < C*k*10^(-k)`. |
| BD2005 | Theorem 2.1 says every irrational fixed orbit `{b^n*xi}` has diameter at least `1/b`, and classifies equality by Sturmian base-`b` expansions. | Salikhov's theorem makes the irrational premise valid for pi; with `b=10`, the orbit is not contained in an interval shorter than `1/10`. | A diameter lower bound of `1/10` is independent of `k`, has no hitting time, and does not imply entry into even one prescribed interval of length `10^(-k)`. No `N,H,B` are supplied. |
| KWON2012 | Theorems 1.1 and 5.1 classify beta-orbits of diameter at most `1/beta` as Sturmian, mechanical, or skew according to the exact cases stated below. | At `beta=10`, irrationality of pi leaves the Sturmian boundary case if its orbit diameter were at most `1/10`. | The exact unmet pi-specific premise for using the classification to rule out the boundary case is a proof that pi's decimal tail is not Sturmian. Even that would yield only diameter `>1/10`, not shrinking-target coverage or T3 sums. |
| BK2017 + BD2005 | Theorem 4.5 computes the irrationality exponent of every Sturmian base-`b` number from its repetition exponent. Together with BD2005 it gives explicit transcendental, finite-type fixed orbits confined to an interval of length `1/b`. | It does not classify pi. It tests whether "finite irrationality measure" could by itself be enough. | The Fibonacci Sturmian decimal has irrationality exponent `phi^2 = 2.618... < 7.6063...` yet its decimal orbit is confined to an interval of length `1/10` and misses shrinking targets. Therefore Salikhov's finite-type information alone cannot imply any T3 certificate. |

No row instantiates T3.

## 5. Exact Quotations And Checks

Line locators refer to `pdftotext -layout` outputs regenerated by
`./reproduce.sh fetch NEW_DIRECTORY`. The retained PDFs are authoritative.
No OCR was needed.

### 5.1 Salikhov: the arithmetic fact actually known for pi

Salikhov states:

> "Theorem 1. For all p, q in N with q >= q_0 the following inequality
> holds: |pi - p/q| >= q^(-nu), where nu = 7.6063... ."

([SAL2008], printed p. 570; extracted lines 7-18.) The final calculation says
the construction proves the inequality for any
`nu > 7.60630852...` (pp. 571-572; lines 117-124). To avoid an endpoint
rounding claim, fix any `mu0 > 7.60630852`.

For an integer `Q` large enough and `p` nearest to `Q*pi`, the theorem gives

```text
||Q*pi|| = Q*|pi-p/Q| >= Q^(1-mu0).
```

At `Q = |h|*10^j`, this is a pointwise lower bound

```text
||h*10^j*pi|| >= (|h|*10^j)^(1-mu0).
```

It prevents an orbit phase from being *too close* to an integer. T3 instead
needs cancellation in

```text
sum_(j<N) exp(2*pi*i*h*10^j*pi)
```

for every `0 < |h| <= H`. A lower bound on each phase's distance from `1`
does not upper-bound the norm of their vector sum.

The mismatch is also visible directly at the target near zero. If
`{10^n*pi} < 10^(-k)`, truncation gives an approximation with exponent
`1+k/n`. Salikhov can rule out such a hit only in the early regime
`k > (mu0-1)*n` (after the source threshold). It gives no existence of a hit.
At the requested deadline `n <= C*k*10^k`, its lower bound is on the vastly
smaller scale `10^(-(mu0-1)*C*k*10^k)`, not `10^(-k)`, and it says nothing
about arbitrary translated decimal cylinders.

### 5.2 Bugeaud--Dubickas: exact constant-diameter theorem

Theorem 2.1 states:

> "Let b >= 2 be an integer and xi be an irrational real number. Then the
> numbers {xi b^n}, n >= 0, cannot all lie in an interval of length strictly
> smaller than 1/b. On the other hand, the real numbers {xi b^n}, n >= 0, are
> all lying in a closed interval I of length 1/b if, and only if,
> xi = g + k/(b-1) + t_b(w), where g is an arbitrary integer, k is in
> {0,1,...,b-2}, and w is a Sturmian word on {0,1}."

It continues:

> "If this is the case, then xi is transcendental..."

([BD2005], printed p. 72; extracted lines 157-166.)

For `b=10` and `xi=pi`, Salikhov discharges irrationality, so the unconditional
conclusion is only

```text
sup_n {10^n*pi} - inf_n {10^n*pi} >= 1/10.
```

This has no `N`, no rate, and no shrinking scale. An orbit can have diameter
`1/10` while remaining in one fixed interval forever; Theorem 2.1 explicitly
classifies uncountably many such orbits. Thus its pi conclusion cannot imply
entry into all `10^k` cylinders by any deadline.

The same paper's Theorem 1.1 gives an algebraic-multiplier result, but its
fixed factor is `F(n)` and, for integer multiplier `10` (a Pisot number), its
extra hypothesis requires `F` not to lie in `Q(10)[X]`. Taking the constant
`F=pi` satisfies that by Salikhov's irrationality conclusion, yet the result remains
the same kind of constant interval-diameter lower bound, not T3 cancellation
([BD2005], p. 71; lines 117-130). No stronger conclusion is inferred.

### 5.3 Kwon: exact low-complexity boundary case

Kwon quotes the integer-base classification as:

> "Theorem 1.1 ([6]). Let beta >= 2 be an integer and xi be an irrational
> number. Suppose that s <= {xi beta^n} <= t for every integer n >= 0. Then
> t-s cannot be smaller than 1/beta. Furthermore,
> s <= {xi beta^n} <= s+1/beta for every integer n >= 0 if and only if
> xi = floor(xi) + (w)_beta for some mechanical word w with irrational
> slope."

([KWON2012], printed p. 868; extracted lines 80-87; punctuation around the
display has been linearized.) His extension states:

> "Theorem 5.1. Let beta > 1 and xi in [0,1]. Suppose
> Diam_beta(xi) <= 1/beta."

and lists exactly three alternatives: a Sturmian expansion with diameter
`1/beta`, a rational-slope mechanical expansion with the displayed periodic
diameter, or an eventually skew expansion with the corresponding tail
diameter ([KWON2012], p. 878; lines 512-551).

This is a deterministic structural theorem, but its implication runs from an
already confined orbit to low symbolic complexity. To use its contrapositive
for pi requires the currently unmet fixed-pi statement that the decimal tail
is not Sturmian, the only irrational boundary case. More importantly, proving only diameter
`>1/10` would leave every `10^(-k)` hitting time uncontrolled. The theorem
contains no finite prefix, discrepancy, exponential sum, or phase-coherence
estimate.

### 5.4 Bugeaud--Kim: finite irrationality measure is not enough

Bugeaud--Kim define the repetition exponent by

```text
rep(x) = liminf_(n->infinity) r(n,x)/n
```

([BK2017], preprint p. 6; lines 226-235). Theorem 4.5 states:

> "Let b >= 2 be an integer and x = x_1 x_2 ... a Sturmian word. Then, the
> irrationality exponent of the irrational number sum_(k>=1) x_k/b^k
> satisfies mu = rep(x)/(rep(x)-1), where the right hand side is infinite if
> rep(x)=1."

([BK2017], pp. 9-10; extracted lines 429-439.) The paper also records exactly
that the Fibonacci word `f` satisfies `rep(f)=phi`, where
`phi=(1+sqrt(5))/2` (p. 7; lines 270-274). Consequently, for

```text
x_F = sum_(j>=1) f_j/10^j,
```

Theorem 4.5 gives

```text
mu(x_F) = phi/(phi-1) = phi^2 = 2.618033... .
```

Taking `g=k=0`, `b=10`, and `w=f` in BD2005 Theorem 2.1 simultaneously
shows that the whole orbit `{10^n*x_F}` lies in one interval of length `1/10`
and that `x_F` is transcendental. Its complement contains decimal cylinders
of all sufficiently fine lengths, so this orbit has no all-cylinder cover at
any deadline.

This is a deterministic obstruction, not an experiment and not a statement
about pi's digits. It proves that even the arithmetic condition

```text
irrationality exponent <= 7.60630853
```

does not force density, shrinking-target hitting, or T3 cancellation for a
base-10 orbit; this counterexample additionally happens to be transcendental
by BD2005. Salikhov's presently verified arithmetic information about pi is
therefore too coarse by itself. A theorem using additional, genuinely
orbit-sensitive hypotheses could still apply; this example does not exclude
one.

## 6. Exact Missing Fixed-Pi Information

Within the documented corpus, a positive route still needs at least one of the
following fixed-pi statements, none supplied by the retained theorems:

1. T3 directly: for one `C` and every `k`, explicit `N,H,B` with
   `N <= C*k*10^k`, `H >= 10^(2k)`, and simultaneous unnormalized sum bound
   `B < C*k*10^(-k)`.
2. A deterministic discrepancy theorem for `{10^n*pi}` strong enough that
   every interval of length `10^(-k)` is hit by `N <= C*k*10^k`, with all
   constants and onset uniform in `k`.
3. A deterministic shrinking-target theorem whose hypotheses include a
   source-verified property of pi stronger than finite irrationality measure
   or transcendence and whose conclusion has the same uniform deadline.
4. An orbit-complexity theorem proving enough distinct and correctly placed
   length-`k` decimal factors by that deadline. Merely proving non-Sturmian or
   superlinear factor complexity would still be far below all `10^k` words
   with a quantitative first-occurrence bound.

The exact obstruction is not that pi lacks a finite irrationality measure; it
has one by SAL2008. The obstruction is that an irrationality measure controls
exceptionally close rational approximations, while T3 requires simultaneous
phase cancellation and positive visits to every translated shrinking target.

## 7. Bounded Conclusion

For the five retained sources, four finite metadata queries, and four screened
citation-chain exclusions recorded in `retrieval_manifest.json`, no theorem
instantiates T3 at `N = O(k*10^k)` and target scale `10^(-k)` for pi.

The strongest applicable deterministic orbit statement is only the
Bugeaud--Dubickas constant diameter bound `>=1/10`. The strongest retained
arithmetic input naming pi is Salikhov's irrationality exponent bound. The
Fibonacci Sturmian decimal gives a source-pinned obstruction showing that a
substantially smaller finite irrationality exponent does not force base-10
orbit density, much less the required quantitative cover.

This negative conclusion is limited to this corpus. It does not assert that no
deterministic theorem outside the search bounds exists, and no almost-everywhere
or finite-computation result has been attributed to pi.

## 8. Replay

From this artifact directory run:

```sh
./reproduce.sh verify
./reproduce.sh fetch /tmp/t9-replay
```

`verify` checks every retained artifact and the pinned canonical, T3, and T4
dependencies. `fetch` requires a new directory, downloads every primary PDF,
checks its SHA-256, regenerates every `pdftotext -layout` extraction, checks
the extraction hashes, and reruns the four mutable metadata queries. Search
responses may change; a changed primary PDF is reported as a source-version
change rather than silently accepted.

## References

- [ABT2024] DOI `10.48550/arXiv.2301.05561`.
- [BD2005] DOI `10.1016/j.crma.2005.06.007`.
- [BK2017] DOI `10.1090/tran/7378`.
- [KWON2012] DOI `10.4134/JKMS.2012.49.4.867`.
- [SAL2008] DOI `10.1070/RM2008v063n03ABEH004543`.

Exact URLs, file names, byte counts, hashes, and theorem locators are in
`retrieval_manifest.json`.
