# T28: Source-Pinned Lacunary-Sum Audit Against T27

Status: `literature-checked` on 2026-07-22 for the primary sources and bounded
searches listed below. This audit proves no statement about the decimal digits
of pi. In particular, it makes no unconditional V1 or V3 claim.

## 1. Immutable target and scope

The canonical source is `knowledge/pi/statements/pi-digits.txt`, SHA-256
`2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825`.
Its canonical V1 asks whether every finite decimal word, including words with
leading zero, occurs contiguously in pi. V1 remains open. The sibling V3 is the
distinct assertion that every digit occurs infinitely often; it also remains
open.

This audit addresses only the analytic premise of accepted T27. It cites,
rather than repeats, the broader post-frontier survey T19:

- `knowledge_library/t19/T19-post-frontier-separation-audit.md`, staged
  SHA-256 `18ac9bea801c28b38122926d91ae745686944091f36617bde000e6d2944d67af`;
- `knowledge_library/t19/HASHES.sha256`, staged SHA-256
  `be89ed4bfe8446ddc6ce5673e6359578793bbbbd14aafc28d4f38877b9f85e34`.

T19 searched pi-specific digit mechanisms. T28 instead performs the narrower
comparison with metric lacunary exponential-sum and discrepancy theorems.

## 2. Exact T27 normalization and ambiguous quantifiers

Put

```text
e(t)       = exp(2*pi*i*t),
S_N(h,x)   = sum_{j=0}^{N-1} e(h*10^j*x),
L_k        = 10^(-k).
```

T27's `piFractionalOrbit j` is `fract(10^j*pi)`. Since `h` is an integer,
periodicity gives

```text
e(h*fract(10^j*x)) = e(h*10^j*x).
```

Thus the sums in this audit are exactly T27's sums, not an approximation.
Negative frequencies satisfy `S_N(-h,x) = conjugate(S_N(h,x))`, so their
norms agree.

For `N > 0`, T27 asks for one common `B` such that

```text
|S_N(h,x)| <= B for every integer h with 0 < |h| <= H,
```

and its displayed strict hypothesis is algebraically equivalent to

```text
H*B + N*10^(2*k)/(H+1) < N.                 (T27-CERT)
```

Indeed, the denominator `N*(H+1)` is positive and
`1/L_k^2 = 10^(2*k)`. Under T27's complete hypotheses, a necessary
condition is

```text
H + 1 > 10^(2*k).                            (H-MIN)
```

This necessity uses the frequency bound, not just the displayed strict
inequality in isolation. If `H>=1`, applying the frequency bound at `h=1`
forces `B>=0`; if `H=0`, `(T27-CERT)` is impossible because
`10^(2*k)>=1`. Negative artificial values of `B` could defeat `(H-MIN)` if
the strict inequality were detached from T27's frequency hypothesis, but
they cannot occur in a T27 certificate.

The literature has several quantifier distinctions that cannot be merged:

1. `for almost every x` does not imply the result for the fixed number pi;
2. an asymptotic limsup gives an `x`- and epsilon-dependent threshold, not a
   displayed checkable finite `N`;
3. a theorem for each fixed `h` can be intersected over a fixed finite `H`,
   but this does not make its exceptional set explicit;
4. a theorem about every fixed gap sequence still usually removes a null set
   after that sequence has been fixed;
5. transcendence of pi does not remove pi from an unspecified null set;
6. proving a certificate for one fixed `k` is not canonical V1, which
   quantifies over all finite lengths.

The index convention in the papers is usually `j=1,...,N`. It matches T27
exactly by taking `n_j = |h|*10^(j-1)`, or, for geometric-progression
discrepancy, by replacing the paper's initial point by `h*x/10`.

## 3. Primary-source pins

| ID | Source and stable locator | Retrieved file | SHA-256 | Extraction |
|---|---|---|---|---|
| EG-I | P. Erdos and I. S. Gal, *On the law of the iterated logarithm. I*, Indagationes Mathematicae 17 / Proceedings 58 (1955), 65-76. DOI <https://doi.org/10.1016/S1385-7258(55)50010-2>. PDF <https://www.renyi.hu/~p_erdos/1955-06.pdf>. | `erdos-gal-1955-part1.pdf` | `a94e2560d886e4de674f678363c596276c73e0e06a492a866239543dee746931` | `pdftotext -layout` file `erdos-gal-1955-part1.txt`, SHA-256 `3930ff1d597d9e0c929097b7a85864d0c1bdec0034b31f529ea919025e7e4416` |
| EG-II | P. Erdos and I. S. Gal, *On the law of the iterated logarithm. II*, Indagationes Mathematicae 17 / Proceedings 58 (1955), 77-84. DOI <https://doi.org/10.1016/S1385-7258(55)50011-4>. PDF <https://www.renyi.hu/~p_erdos/1955-07.pdf>. | `erdos-gal-1955-part2.pdf` | `c638ec58e455da94a2406b858e0a5b9ce3271954e77c38eec10581abf0ed7ff6` | `pdftotext -layout` file `erdos-gal-1955-part2.txt`, SHA-256 `eaf4be26d9621424735aba92b04e7b66835c18b62107e0173e5cb19e52964f20` |
| PH | W. Philipp, *Limit theorems for lacunary series and uniform distribution mod 1*, Acta Arithmetica 26 (1975), 241-251. DOI <https://doi.org/10.4064/aa-26-3-241-251>. PDF <https://www.impan.pl/shop/publication/transaction/download/product/100600?download.pdf>. | `philipp-1975-lacunary.pdf` | `4d0edc8170fe1ddf368ada0fd64ed7ec48411840ab6c07fdd658e44fbae84e3a` | The PDF is an image scan. `pdftotext -layout` retained only page breaks in `philipp-1975-lacunary.txt`, SHA-256 `7b2aa16484b6ad79ef5bec51da3501f5079367b625da44bf97468422d27e8e95`. The rendered pages cited below are authoritative. |
| FU | K. Fukuyama, *The law of the iterated logarithm for discrepancies of {theta^n x}*, Acta Mathematica Hungarica 118 (2008), 155-170. DOI <https://doi.org/10.1007/s10474-007-6201-8>. Stable repository record <https://hdl.handle.net/20.500.14094/90003836>. Accepted-manuscript PDF <https://da.lib.kobe-u.ac.jp/da/kernel/90003836/90003836.pdf>. | `fukuyama-2008-geometric-discrepancy.pdf` | `59b263e7d74aa627606181646c75c02803c41d42af4d1780f7ff8de28f917266` | `pdftotext -layout` file `fukuyama-2008-geometric-discrepancy.txt`, SHA-256 `f0f50d8450f05bbe5bcf78d76a5448232631c3c974369103048f6e4a0064c808` |

The EG paper is split into two separately pinned parts because Part I states
the theorem and develops the moment and measure estimates, while Part II
completes the proof.

## 4. Theorem-by-theorem audit

Here `D_N` denotes normalized extreme discrepancy, so `N*D_N` is the
unnormalized counting error.

| Result | Exact published statement and constants | Quantifiers and effectiveness | Match to `10^j`, `h`, `k`, `H`, `N` | Applies to `x = pi`? |
|---|---|---|---|---|
| EG-I main theorem, p. 65; proof completed in EG-II | If `0 < n_1 < n_2 < ...` and `n_(j+1)/n_j >= q > 1`, then `limsup_(N->infinity) |sum_(j=1)^N e(n_j*x)| / sqrt(N*log log N) = 1` for almost all `x`. The `n_j` are positive real numbers; the LIL constant is exactly `1`. | For each fixed sequence and fixed `q`, Lebesgue-almost every `x`. Equivalently, for every `epsilon > 0`, the upper bound `(1+epsilon)*sqrt(N log log N)` holds after an unspecified threshold depending on `x`, the sequence, and epsilon. No exceptional set or numerical pointwise threshold is supplied. | For any fixed positive `h`, take `n_j=h*10^(j-1)` and `q=10`; negative `h` follows by conjugacy. For fixed finite `H`, intersect the `H` full-measure sets and take their maximum threshold. Then one common `B=(1+epsilon)*sqrt(N log log N)` works eventually for all `0<|h|<=H`. For any fixed `k`, choose any `H` satisfying `(H-MIN)`; because `H*B/N -> 0`, `(T27-CERT)` holds for all sufficiently large `N`. | **No.** The exact sequence and frequency parameters match, but the theorem's almost-everywhere set is not known to contain pi. The threshold is also not numerically checkable for pi. |
| EG-I Lemma 7, printed p. 74 | Let `F(N,x)=|sum_(j=1)^N e(n_j*x)|` and let `phi(t)` be the measure in `[alpha,beta]` where `F(N,x) >= sqrt(t*N*log log N)`. If `beta-alpha >= 1/(n_1*sqrt(N))` and `N>=N_0(q)`, then `phi(t) <= (beta-alpha)*18*log log N/(log N)^t` for `0<=t<=3`, and `phi(t) <= (beta-alpha)*6*log log N/t^(2 log log N)` for `3<=t<=N`. | A finite exceptional-measure estimate with explicit `18` and `6`. The threshold `N_0(q)` is independent of the interval and sequence, but the paper does not give its numerical value. It controls measure, not a named point. | On `[0,1]`, use `n_j=h*10^(j-1)` and `q=10`, then take a union bound over positive `1<=h<=H` (negative events coincide). With `B=sqrt(t*N*log log N)`, the bad-set measure is at most `H` times the displayed bound. If that upper bound is below `1`, some `x` obey all frequency bounds; if `(T27-CERT)` also holds, some `x` has a T27 certificate. The unknown `N_0(10)` prevents a fully numerical finite witness from this lemma alone. | **No.** A small exceptional measure, even an explicit one, cannot certify that pi is outside the exceptional set. |
| PH Theorem 1, (1.5), pp. 241-242 | For an integer sequence with `n_(j+1)/n_j >= q>1`, for almost all `x`, `32^(-1/2) <= limsup N*D_N({n_j*x})/sqrt(N*log log N) <= C`, where `C <= 166 + 664/(sqrt(q)-1)`. The note added on p. 250 reports an improvement of the lower constant to `1/4`; it does not change the upper bound used here. | Almost every `x`; asymptotic limsup. The upper coefficient is explicit in `q`, but the theorem gives no explicit exceptional set and no numerical pointwise threshold. | Set `n_j=10^(j-1)`, so `q=10` and `C_10 <= 166+664/(sqrt(10)-1)`. Equation (3.9), below, turns this into the eventual common bound `B=sqrt(32)*(C_10+epsilon)*sqrt(N log log N)` for each fixed frequency after replacing `x` by `h*x`; finite intersection handles fixed `H`. This eventually satisfies `(T27-CERT)` whenever `(H-MIN)` holds, but is much weaker than EG's direct constant. | **No.** The obstruction is the almost-everywhere quantifier, not the gap ratio or radix. |
| PH deterministic inequality (3.9), p. 250 | For every finite real sequence `(x_j)`, `|sum_(j<=N) e(x_j)| <= sqrt(32)*N*D_N(x_j)`. The note added reports that `sqrt(32)` can be improved to `4`. | Deterministic, finite, and valid for every point sequence. It is effective once an actual discrepancy bound is known. It supplies no discrepancy estimate by itself. | Taking `x_j=h*10^(j-1)*pi` gives a true finite implication for pi, but no retained source bounds that discrepancy at pi. It therefore cannot supply T27's `B` unconditionally. | **Conditionally only.** It applies to pi as an inequality, but its right side is not known to be small enough for `(T27-CERT)`. |
| FU Theorem and Corollary, manuscript pp. 1-2 / journal pp. 155-156 | For every fixed `theta>1`, for almost every `x`, both barred limits (limsup) `N*D_N({theta^j*x})/sqrt(2*N*log log N)` and the star-discrepancy version equal `Sigma_theta`. If some positive power of `theta` is rational, write `theta=(p/q)^(1/r)`, where `r` is the least positive integer with `theta^r` rational, `p,q` are positive integers, and `gcd(p,q)=1`. If `p>=4` is even and `q=1`, then `Sigma_theta = (1/2)*sqrt((p+1)*p*(p-2)/(p-1)^3)`. Specializing further to `r=1`, `theta=p=10` gives `Sigma_10=sqrt(220)/27`, exactly. | Almost every `x`. The LIL constant is exact, but no convergence rate, exceptional set, or numerical pointwise threshold is supplied. The assertion concerns the initial point `x`; it is neither an algebraic-input theorem nor a theorem for every transcendental input. | To represent T27 frequency `h` and indices `j=0,...,N-1`, use the paper's `theta=10` and initial point `y=h*x/10`. Scaling preserves null sets, and finite intersection handles fixed `H`. Combining with PH (3.9), for every epsilon and almost every `x`, eventually `B=sqrt(32)*(Sigma_10+epsilon)*sqrt(2*N*log log N)` works simultaneously for `0<|h|<=H`. For fixed `k` and `(H-MIN)`, this eventually satisfies `(T27-CERT)`. | **No.** The exact base-10 constant does not identify pi as a good initial point; setting `y=h*pi/10` is precisely the unsupported specialization. |

## 5. Explicit parameter derivation

The strongest retained direct sum theorem is EG. Fix a word length `k` and
choose an integer `H` with

```text
H + 1 > 10^(2*k).
```

Define the positive margin

```text
delta = 1 - 10^(2*k)/(H+1).
```

For any `epsilon>0`, EG gives, for almost every `x`, an unspecified
`N_0(x,H,epsilon)` such that for every `N>=N_0`,

```text
max_{0<|h|<=H} |S_N(h,x)| <= B_N,
B_N = (1+epsilon)*sqrt(N*log log N).
```

Substituting this common bound into T27 gives exactly

```text
H*(1+epsilon)*sqrt(N*log log N) < delta*N.
```

The left side divided by `N` tends to zero. Therefore, for each fixed `k`,
for almost every `x` there exist `H,N,B_N` that satisfy every analytic
hypothesis of T27. This stated quantifier order is all that T28 needs. A
single conull set for all `k` could be obtained by an additional countable
intersection, but is not used here. The result is a genuine parameter match,
but only with an almost-everywhere `x`; it does not supply those parameters
for pi.

Fukuyama gives the same qualitative parameter match through discrepancy with
the explicit base-10 constant `sqrt(220)/27`, but the deterministic
discrepancy-to-sum coefficient makes that route numerically weaker than EG.

No effectiveness issue can repair the main quantifier mismatch. Even if every
threshold in the metric proofs were made numerical and every bad-set measure
were explicitly tiny, a singleton such as pi could still lie in every bad
set. Conversely, an applicable fixed-pi theorem with any common bound
`B=o(N/H)` and `H+1>10^(2*k)` would create a concrete T27 proof target for
that `k`.

## 6. Input classification

| Input class for `x` | What the retained theorems prove | Consequence for pi |
|---|---|---|
| Lebesgue-almost every real `x` | EG square-root LIL; PH discrepancy LIL bounds; FU exact geometric discrepancy LIL. | A full-measure assertion cannot be specialized to a named point. |
| Every fixed real `x` | Only PH (3.9), which bounds a sum by the point sequence's still-unknown discrepancy. Universal cancellation is false, for example at rational inputs. | No usable fixed-pi upper bound. |
| Algebraic `x` | No retained theorem is an algebraic-input theorem. Rational algebraic inputs already show that no unrestricted algebraic statement is possible. | Pi is transcendental, so an algebraic-only theorem would not apply anyway. |
| Almost every transcendental `x` | Yes, as a consequence of the metric theorem and countability of algebraic numbers. | This still says nothing about the specified transcendental number pi. |
| Fixed `x=pi` | None of EG, PH Theorem 1, or FU places pi outside its exceptional set. | T27's finite exponential bounds remain unproved. |

## 7. Bounded search record

These searches were retrieved on 2026-07-22. They are finite metadata
searches, not evidence that no other theorem exists.

| Database | Exact query and bound | Retained response |
|---|---|---|
| Crossref | `query.bibliographic=lacunary exponential sums geometric progressions discrepancy`, first 20 selected metadata records. The endpoint reported 205936 ranked matches; the returned ranking was noisy and included arithmetic-progression papers. | `search-crossref.json`, SHA-256 `2f4b15f2bb581c377867228d048214419aec1ddc6dbfb642c859bcea408165cf` |
| Crossref | `query.title=law of the iterated logarithm discrepancies theta n x`, first 20 selected metadata records. The exact Fukuyama DOI appeared among the returned records. | `search-crossref-title.json`, SHA-256 `39cd5c2a55645667404f5b974bdfd0cccf8868b065eaef7902e3202e086f8eef` |
| OpenAlex | Full-text metadata search `lacunary exponential sums geometric progressions discrepancy`, first 25 records; 15 were returned. Relevant results included later metric geometric-progression papers and a lacunary-sums survey. | `search-openalex.json`, SHA-256 `1b28f4067ab0b2e494e323eba473a1892ad6cb9348c30d185c9b8cde92d71fd1` |

The candidate set was formed from these bounded outputs, references in the
retained papers, and direct DOI/repository checks. EG was retained because it
directly bounds T27's sums; PH because it gives the general discrepancy scale
and a deterministic sum-discrepancy bridge; FU because it computes the exact
base-10 geometric-progression discrepancy constant. Later papers that restate
or refine related metric constants were not duplicated once FU supplied the
exact base-10 theorem. Failure to retain another candidate is not an absence
claim.

## 8. Reproduction and conclusion

From this artifact directory run:

```sh
./reproduce-t28.sh verify
./reproduce-t28.sh fetch /tmp/t28-reproduction
```

`verify` checks the retained files against `HASHES.sha256` and checks the
canonical statement and cited T19 files against `DEPENDENCIES.sha256` without
duplicating accepted library content. `fetch` requires a new empty output
path, downloads the four PDFs, reruns `pdftotext -layout`, and repeats the
three metadata requests. It then checks the byte-stable downloads and stable
Fukuyama extracted text against `FETCH_STABLE_HASHES.sha256`, and prints all
fresh hashes. Publisher files and API rankings can change; a changed fresh
hash is a detectable source-version or index change, not a reason to alter the
retained pin. Philipp's scan must be checked visually at printed pp. 241-243
and 250 because Poppler extracts no words from it.

A replay during this audit observed one concrete mutable-file case. Kobe's
repository returned Fukuyama's same 142460-byte, 13-page encrypted PDF with
fresh SHA-256
`77fd57f967c2e2e823fdaff70eae00eaf75d725d1d5921f036c261b9209f9553`
instead of the retained retrieved-file pin, while both copies produced the
identical `pdftotext -layout` SHA-256
`f0f50d8450f05bbe5bcf78d76a5448232631c3c974369103048f6e4a0064c808`.
Repeated repository downloads were dynamically re-encrypted and need not be
byte-identical. Accordingly, `verify` reproduces the exact retained PDF hash;
a fresh-content check uses the stable DOI/repository record, page count, and
identical extracted-text hash. The live OpenAlex response also changed on
replay, as the search-log warning anticipates. These mutable responses do not
alter the theorem transcription, but they prevent a claim that every future
redownload will have the retained byte hash.

The final adversarial replay encountered a transient HTTP 429 during the
bounded metadata requests; the script's four retries recovered and completed
the run. That replay again passed every entry in
`FETCH_STABLE_HASHES.sha256`. Its dynamically re-encrypted Fukuyama PDF had
SHA-256 `1b301db93e9b3f2928c98281d07e1271e3251c5dc9e64f04d9e6382b0418a169`
with the same extracted-text hash, and its fresh OpenAlex response had
SHA-256 `daf573cb45e2ab8c759340367bb6df4a417e821bd9a46d85404a75b99f074c78`.
Both retained Crossref responses redownloaded byte-identically on that replay.

The audit outcome is:

1. For each fixed `k`, the published metric theorems instantiate T27's finite
   bounds for almost every `x`, after the explicit choices above.
2. They do not instantiate T27 at `x=pi`: the exact fatal mismatch is the
   almost-everywhere quantifier. Their non-explicit pointwise thresholds are a
   second effectiveness mismatch for a numerical certificate.
3. No retained theorem is a fixed-pi or algebraic-input estimate. Pi's
   transcendence does not bridge a metric exceptional set.
4. This is `literature-checked` progress on G18, not a proof of canonical V1,
   sibling V3, normality of pi, or any unconditional decimal occurrence.
