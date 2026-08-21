# T44: source-pinned multiplicative-rigidity applicability audit

Status: `literature-checked` on 2026-08-03 for the exact sources and bounded
searches recorded below. This is an applicability audit, not a proof about any
named constant.

## 1. Immutable target and exclusions

The vendored canonical statement is `pi-digits.txt`, SHA-256
`2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825`.
Its canonical V1 asks whether every finite decimal word, including words with
leading zeroes, occurs contiguously in the decimal expansion of pi. The source
also records distinct sibling variants V2 and V3.

This audit makes **no unconditional claim** about pi, `JMix(pi)`, V1, or V3.
In particular, an almost-everywhere conclusion is never specialized to a named
point. A conditional route below is a condition for a generic real `x` or for
almost every point of a specified measure; it is not evidence that the condition
holds at pi.

The exact local interfaces compared here are vendored byte-for-byte. Their
recorded verification level is `machine-checked`; this literature bundle pins
and inspects their definitions but does not independently recompile their
transitive Lean imports:

| Interface | File | SHA-256 | Role |
|---|---|---|---|
| T20 | `BaseTenOrbitDensity.lean` | `202d6db7dfc2f19db81c3cb96b856d36969652e54099c43e0d51b6ab62913126` | `BaseTenOrbitDense x` is the metric density of `fract(10^k x)` in `[0,1]`; for nonnegative `x`, it is equivalent to occurrence of every finite decimal word. |
| T37 | `CrossBaseCarry.lean` | `be14ac145519d4a9e9f394365ef4852ad8196e37f3ddb7ee682b31b0dd0459a6` | Exact base-16/base-10 cylinders, carries, synchronous transitions, `JMix`, and the conditional bridge `x >= 0 and JMix x -> BaseTenOrbitDense x`. |

## 2. Exact T37 normalization and ambiguous identifications

Write `T_b(t) = b*t mod 1` on the circle `K = R/Z`. T37 defines

```text
CrossBaseTransition x n A m D j
  := T_16^j(x) lies in the base-16 cylinder I_16(n,A)
     and T_10^j(x) lies in the base-10 cylinder I_10(m,D).
```

Its frequency is the average of this indicator over `0 <= j < N`, and

```text
JMix x := for every valid n,A,m,D,
  frequency_N(x;n,A,m,D) -> 16^(-n) * 10^(-m).
```

Thus `JMix` is a pointwise, synchronous, one-parameter product-frequency
assertion for

```text
j |-> (T_16^j(x), T_10^j(x))
```

under the single torus map `F(u,v) = (T_16(u),T_10(v))`. Taking the empty
base-16 cylinder gives the decimal marginal used by T37's existing
`JMix_implies_baseTenOrbitDense` when `x >= 0`; no rigidity theorem is needed
after `JMix` and this sign premise have been assumed. Circle representatives
in `[0,1)` satisfy the sign premise in the measure-theoretic rows below.

The following objects must not be silently identified:

1. The synchronous orbit above is not the two-parameter circle orbit
   `{T_16^a T_10^b(x) : a,b >= 0}`.
2. An empirical measure on `K^2` invariant under `F` is not a probability
   measure on `K` invariant separately under both `T_16` and `T_10`.
3. Nonempty overlap of one hexadecimal cylinder and one decimal cylinder,
   characterized by T37's carry inequalities, does not imply that an orbit
   visits either cylinder.
4. A closed orbit closure invariant under `T_10` is not automatically invariant
   under `T_16`.
5. A theorem holding for `mu`-almost every point does not hold at a specified
   point without a separate typicality argument.
6. Positive entropy of a measure is not supplied by unbounded exact carries,
   by infinite continuation-language index, or by multiplicative independence.

The integers 10 and 16 are multiplicatively independent: if
`10^a = 16^b` for positive `a,b`, comparison of the exponent of the prime 5
gives `a=0`, a contradiction. They are not coprime, since `gcd(10,16)=2`.

## 3. Source pins

All quotations are checked against the retained file. PDF text locations refer
to the reproducible `pdftotext -layout` output whose expected hash is recorded
below. Furstenberg's scan has visibly
damaged character spacing; quotations from it were also checked on the rendered
journal page. Formula glyphs and whitespace are normalized to readable ASCII,
without changing words or quantifiers.

| ID | Source and stable locator | Retrieved file and SHA-256 | Exact location |
|---|---|---|---|
| F67 | Harry Furstenberg, *Disjointness in Ergodic Theory, Minimal Sets, and a Problem in Diophantine Approximation*, Mathematical Systems Theory 1 (1967), 1-49. DOI <https://doi.org/10.1007/BF01692494>. Publisher record <https://link.springer.com/article/10.1007/BF01692494>. Retrieved institutional scan <https://mathweb.ucsd.edu/~asalehig/F_Disjointness.pdf>. | `furstenberg-1967-disjointness.pdf`, `cd07faa4521080272cf2c303ee4e3a41ee6a3ba9e6aea114604becaca0ba9358`; generated extraction `furstenberg-1967-disjointness.txt`, `3e5a82a8c8861c51eca6931e2f39f22f6466427d597caac2d3e0583517ac5c4b`. | Definition IV.1, Lemma IV.2, Proposition IV.2, and Theorem IV.1, printed pp. 47-48, extracted lines 2182-2258; Theorem I.1, printed p. 12, extracted lines 514-544. |
| R90 | Daniel J. Rudolph, *x2 and x3 invariant measures and entropy*, Ergodic Theory and Dynamical Systems 10 (1990), 395-406. DOI <https://doi.org/10.1017/S0143385700005629>. Publisher PDF <https://www.cambridge.org/core/services/aop-cambridge-core/content/view/64243AD8323B37089540F911F8CC77EB/S0143385700005629a.pdf/2-and-3-invariant-measures-and-entropy.pdf>. | `rudolph-1990-times2-times3.pdf`, `9016e14ea8a3125dbea8532c6f8b2230fb24a33fe5e8818db8bcf0f7a7b57c85`; generated extraction `rudolph-1990-times2-times3.txt`, `0ad910b573346e14853030e0124f3c239eb7dd8532f542e9f7983b4928907de7`. | Definition of `M,M_0`, printed p. 399, extracted lines 213-216; Theorem 4.9 and Corollaries 4.10-4.11, printed pp. 405-406, extracted lines 553-583. |
| J92 | Aimee S. A. Johnson, *Measures on the circle invariant under multiplication by a nonlacunary subsemigroup of the integers*, Israel Journal of Mathematics 77 (1992), 211-240. DOI <https://doi.org/10.1007/BF02808018>. Publisher record <https://link.springer.com/article/10.1007/BF02808018>. | `johnson-1992-publisher.html`, `bf1a12ca6d4f6a00884de2c274e7ce238c3ef4cabe77af1b1e1ecb3a8e02b4a6`; Crossref metadata `johnson-1992-crossref.json`, `5d500dd8c28293f39258e4c6f96d0eae8a9442fc15b2bb6308a7ea89fde06c06`. | Exact publisher abstract at HTML line 788. The full publisher PDF was subscription-only, so no internal theorem number or page quotation is claimed. |
| H95 | Bernard Host, *Nombres normaux, entropie, translations*, Israel Journal of Mathematics 91 (1995), 419-428. DOI <https://doi.org/10.1007/BF02761660>. Publisher record <https://link.springer.com/article/10.1007/BF02761660>. | `host-1995-publisher.html`, `e820e3f9e394e6976e4c726439eb7237dc8c732560f0e4fbe29b427f67ca20fb`; Crossref metadata `host-1995-crossref.json`, `968e2c6e400b83d5b7039d53291ebd07365a05866e30912fdb4c06358b336f28`. | Exact publisher abstract at HTML line 803. The exact theorem hypothesis is quoted from A20's explicit restatement of Host at extracted lines 35-41, because the original full PDF was subscription-only. |
| H22 | Michael Hochman, *A short proof of Host's equidistribution theorem*, Israel Journal of Mathematics 251 (2022), 527-539. DOI <https://doi.org/10.1007/s11856-022-2444-x>. Versioned preprint <https://arxiv.org/abs/2103.08938v2>. PDF <https://arxiv.org/pdf/2103.08938v2>. | `hochman-2022-host-equidistribution-v2.pdf`, `2fa94bec2580725a6b2d3e83761af1510f86061a6090528350c44ea785087d0b`; generated extraction `hochman-2022-host-equidistribution-v2.txt`, `013c44f31d7a2be36d09d060cf49ab2722c70dcf74989b885ba9d21bf1c080e5`. | Theorem 1.1, preprint p. 2, extracted lines 51-62. |
| A20 | Amir Algom, *A simultaneous version of Host's equidistribution Theorem*, Transactions of the AMS 373 (2020), 8439-8462. DOI <https://doi.org/10.1090/tran/8173>. Versioned preprint <https://arxiv.org/abs/1904.12506v1>. PDF <https://arxiv.org/pdf/1904.12506v1>. | `algom-2020-simultaneous-host-v1.pdf`, `7804f0c496c494353719c18895296086f9fde5b9c3b0047b00fe9698395d18d2`; generated extraction `algom-2020-simultaneous-host-v1.txt`, `6f3e07aa72818c7a92cd04f424c6380d51a009cb7dd80c6ed8ea84853344b4a0`. | Host restatement, preprint p. 1, extracted lines 35-41; Theorem 1.1, preprint pp. 1-2, extracted lines 67-90. |

## 4. Theorem-by-theorem verdict matrix

`Applicable conditional route` means the cited theorem gives a substantive
condition, not mentioning T20 density as a premise, from which T20 density
follows. `Mismatch` records the first exact hypothesis absent from T37; later
missing hypotheses are retained to prevent a partial match from being
overstated.

| Row | Theorem | Arithmetic/map match | Measure, invariance, entropy, or genericity map to T37 | Bounded verdict |
|---|---|---|---|---|
| F67-IV.1 | Nonlacunary semigroup orbit density / closed-set rigidity | `S=<10,16>` is nonlacunary; both act on the same circle. | For `C_10(x)=closure{T_10^j x}`, forward `T_10` invariance is automatic. T37 does **not** give forward `T_16(C_10(x)) subset C_10(x)`. No measure or entropy is needed. | **Applicable conditional route:** if `x` is irrational and `C_10(x)` is forward `T_16`-invariant, then `C_10(x)=K`, hence T20 orbit density. The additional invariance is exact and non-tautological; it is not established by T37. |
| R90-4.9/4.11 | Positive-entropy common invariant measure rigidity | Theorem 4.9's coprime hypothesis fails for 10 and 16, but Corollary 4.11 covers them with `u=2,v=5`, exponent vectors `(4,0),(1,1)`, determinant `4`. | **First failure:** T37 supplies no probability measure on one circle invariant under both maps. It also supplies no joint-action ergodicity or positive entropy. A torus empirical measure from the synchronous pair is a different object. Even a conclusion `mu=lambda` would need a separate statement that the fixed `x` is generic for `mu`. | **Mismatch at common circle-measure invariance.** Corollary 4.11 removes the arithmetic obstacle but not the structural one. Assuming `JMix` would already give the desired decimal marginal and would make this use tautological. |
| J92 | Nonlacunary-semigroup positive-entropy measure rigidity | `S=<10,16>` is a nonlacunary subsemigroup. | **First failure:** no `S`-invariant probability measure on the circle is defined by T37. Semigroup ergodicity and positive entropy are also absent. | **Mismatch at common circle-measure invariance.** Johnson generalizes the arithmetic scope, not the missing bridge from a fixed synchronous orbit to a common invariant measure. |
| F67-I.1 | Positive-entropy processes cannot be disjoint | It is a general process theorem, not specific to 10 and 16. | **First failure:** `CrossBaseTransition` is a predicate for one deterministic point and time, not a pair of stationary probability processes. T37 provides neither process entropy nor a joining classification. Moreover, the theorem concludes non-disjointness, not uniqueness of the product joining. | **Mismatch at stationarity/process structure.** This theorem blocks, rather than supports, an argument that positive entropy alone forces product joining behavior. |
| H95 | Original coprime Host normality criterion | The direct substitution `p=16,m=10` fails because `gcd(16,10)=2`; however, `p=3,m=10` satisfies the theorem and still targets the decimal orbit. | Requires a `T_3`-invariant ergodic positive-entropy measure, absent from T37, and concludes only for `mu`-almost every `x`. | **Applicable conditional route at measure-class level:** for every such `T_3` measure, base-10 normality and hence T20 density hold for `mu`-almost every `x`. This supplies neither a fixed-point specialization nor `JMix`; H22 is the correct direct 16/10 extension. |
| H22-1.1 | General Host equidistribution theorem | `a=16,b=10` are multiplicatively independent, so the map hypothesis matches. | Requires a probability measure invariant, ergodic, and positive-entropy under `T_16`; T37 supplies none. Its conclusion holds for `mu`-almost every `x`, not every specified point. | **Applicable conditional route at measure-class level:** for every such `mu`, T20 density holds for `mu`-almost every `x` because base-10 equidistribution implies density. For a fixed `x`, the first unresolved specialization is membership in the theorem's conull set, after constructing the required measure. This does not imply `JMix`. |
| A20-1.1(2) | Simultaneous Host / diagonal joining equidistribution | Choose source map `p=3`, target maps `m=16,n=10`. Then `m>n>1`, `16` is independent of 3, and 10 is independent of 3. | Requires a `T_3`-invariant ergodic measure of positive dimension (equivalently here positive entropy), absent from T37. The conclusion is for `mu`-almost every `x`, so no named point follows. | **Applicable conditional route at measure-class level:** for `mu`-almost every `x`, weak-* convergence of the diagonal pair orbit to `lambda x lambda` gives every T37 cylinder-rectangle frequency and hence `JMix x`, because those half-open rectangles have product-measure-zero boundary. T37 then gives T20 density. No T37 hypothesis establishes the required measure or fixed-point typicality. |

## 5. Exact statements and hypothesis checks

### F67-IV.1: topological times-p/times-q rigidity

F67, Definition IV.1, printed p. 47:

> "A multiplicative semigroup Sigma of integers is lacunary if all the members
> of Sigma+ are powers of a single integer a. Otherwise, Sigma is
> non-lacunary."

F67, Lemma IV.2, printed pp. 47-48:

> "Let Sigma be a non-lacunary semigroup and let A be a closed
> Sigma-invariant subset of K with the property that 0 is a non-isolated point
> of A. Then A=K."

F67, Proposition IV.2 and Theorem IV.1, printed p. 48:

> "If Sigma is a non-lacunary semigroup of integers, the only minimal sets in
> K for Sigma are finite sets (of rationals)."

> "If Sigma is a non-lacunary semigroup of integers and alpha is an
> irrational, then Sigma alpha is dense in K."

The proof uses forward invariance (`sA subset A`), not equality. Apply the
theorem only conditionally: if `C_10(x)` is also forward invariant under
`T_16`, then it contains every `T_16^a T_10^b(x)`. For irrational `x`, F67-IV.1
makes this two-parameter set dense, forcing `C_10(x)=K`. This is precisely T20
orbit density for `x`. T37's carry equations and synchronous pair orbit do not
establish the extra forward invariance.

F67 explicitly limits the conclusion on printed p. 49:

> "We point out that the equidistribution conclusion cannot be made in the
> same generality."

Thus F67-IV.1 supplies density, not `JMix` frequencies.

### R90-4.9/4.11: Rudolph's positive-entropy theorem

R90 defines its measure class on printed p. 399:

> "Let M be the space of all T0 and S0 invariant borel probability measures
> on [0,1). This is a weakly compact convex space. The extreme points, M0, are
> the ergodic measures."

R90, Theorem 4.9, printed p. 405:

> "If GCD(p,q)=1 and mu in M0 but mu != m, then
> h_mu(T,P)=h_mu(S,P)=0."

R90, Corollary 4.11, printed p. 406 (formula typography normalized from the
rendered PDF):

> "If GCD(u,v)=1, u,v != 1 and p=u^(n1)v^(m1), q=u^(n2)v^(m2), where
> n1*m2-m1*n2 != 0, then Theorem 4.9 holds for p and q."

Set `u=2,v=5,p=16,q=10`. The arithmetic hypotheses pass. The first T37
mismatch remains the absence of a common invariant probability measure on the
circle. The exact signed carry at one cylinder pair does not define such a
measure, and an `F`-invariant measure on `K^2` is not one.

### J92: Johnson's nonlacunary-semigroup theorem

The exact primary publisher abstract states:

> "Let S be a nonlacunary subsemigroup of the natural numbers and let mu be an
> S-invariant and ergodic measure. Using entropy arguments on a symbolic
> representation of the inverse limit of this action, we show that if any
> element in S has positive entropy with respect to mu, then mu is Lebesgue."

The full paper was not openly retrievable in this bounded run, so this audit
does not invent an internal theorem number or quote unseen pages. The publisher
statement is enough for the applicability decision: nonlacunarity passes for
`<10,16>`, while the first substantive premise, an `S`-invariant circle
measure, is absent from T37.

### F67-I.1: disjointness does not supply product genericity

F67, Theorem I.1, printed p. 12:

> "Two processes with positive entropy cannot be disjoint."

F67's Definition I.1, printed pp. 4-5, defines disjointness by requiring every
common extension to induce the product/independent coupling. The theorem says
positive entropy prevents that uniqueness. It cannot be used to infer that the
specific diagonal pair orbit in T37 is generic for product measure. The first
formal mismatch is that T37 has no stationary process or invariant process
measure before `JMix` is assumed.

### H95 and H22: pointwise normality from entropy

The exact H95 publisher abstract says:

> "We get a criterium for mu-almost every point to be normal in a basis q
> prime to p, and generalizations of the result of D. Rudolph about measures
> which are invariant by multiplication by p and q."

A20 gives the explicit theorem restatement on preprint p. 1:

> "Let p,m >= 2 be integers such that gcd(p,m)=1. Let mu be Tp invariant
> ergodic measure with positive entropy. Then mu almost every x is normal in
> base m."

The direct 16/10 substitution fails at coprimality. Nevertheless H95 is an
applicable measure-class route with `p=3,m=10`: it gives base-10 normality and
hence T20 density for almost every point of every `T_3`-invariant ergodic
positive-entropy measure. T37 provides no such measure or fixed-point
typicality, and the theorem does not give joint base-16/base-10 frequencies.

H22, Theorem 1.1, provides the applicable general form using the T37 bases
directly:

> "If mu is a probability measure on R/Z that is invariant, ergodic and has
> positive entropy under an endomorphism times a, then mu-a.e. point
> equidistributes for Lebesgue measure under times b, provided a and b are
> multiplicatively independent."

With `a=16,b=10`, the arithmetic condition passes. The result yields decimal
equidistribution, hence T20 density, for almost every point of any measure
satisfying the three stated dynamical hypotheses. It gives no full
base-16/base-10 joint rectangle frequencies and no specialization to a fixed
point.

### A20-1.1(2): a genuine joint-frequency route

A20, Theorem 1.1, preprint pp. 1-2:

> "Let mu be a Tp invariant ergodic measure with dim mu > 0. Let m > n > 1 be
> integers such that m is independent of p. ... If n is independent of p then
> (1/N) sum_(i=0)^(N-1) delta_(Tm^i(x),Tn^i(x)) -> lambda x lambda, for mu
> almost every x."

The source immediately states that positive dimension and positive entropy are
equivalent in this setting. Setting `p=3,m=16,n=10` satisfies all arithmetic
hypotheses. Weak-* convergence gives the limit of indicators of each T37
cylinder rectangle because its boundary is a finite union of vertical and
horizontal line segments and has `lambda x lambda` measure zero. The rectangle
has measure exactly `16^(-r)10^(-s)`. Therefore the theorem's conclusion is
exactly T37's `JMix x` for almost every `x` in the stated measure class.

This is the closest retained rigidity/joining result to T37. Its missing input
is not a carry identity: it is a positive-entropy ergodic `T_3`-invariant
measure together with the theorem's almost-everywhere point selection.

## 6. Prior program audits cited, not repeated

This item does not redo the following bounded searches:

| Item | Cited scope | Staged SHA-256 |
|---|---|---|
| T12 | Failure of unrestricted transfer from base-2 normality to decimal normality or disjunctivity. | `655ff6e76113bc0d28bdb1b7ae9ba3b79dd0a932a816e4fd01ac68354f90cd0f` |
| T19 | Bounded post-frontier search for pi-specific decimal mechanisms. | `18ac9bea801c28b38122926d91ae745686944091f36617bde000e6d2944d67af` |
| T28 | Metric lacunary estimates match generic geometric orbits but cannot be specialized to a named point. | `4845c8661303b873bc4bb38dc8ee1005695fdd62b1fe4d16b36eaee61244abbd` |
| T35 | Theorem-level novelty/context audit for T20 and related interfaces. | `3bf9e00b6149b57813c87c14946377d7bed1bf9bdaf2e662704a3ed1099120dc` |

These citations delimit overlap only. T44's theorem statements and verdicts
are checked against the newly retained sources above.

## 7. Bounded search record

Search date: 2026-08-03. Each metadata query retained only the first 20 ranked
records. Candidate selection also followed references in F67, R90, H22, and
A20 and directly checked the DOI records listed in Section 3.

| Database | Exact query URL | Retained response |
|---|---|---|
| OpenAlex | <https://api.openalex.org/works?search=Furstenberg%20times%20p%20times%20q%20closed%20invariant%20set&per-page=20&select=id,doi,title,publication_year,primary_location,open_access> | `bounded-searches.tar.gz::searches/openalex-closed-set.json` |
| OpenAlex | <https://api.openalex.org/works?search=times%20p%20times%20q%20invariant%20measure%20entropy%20Rudolph%20Johnson&per-page=20&select=id,doi,title,publication_year,primary_location,open_access> | `bounded-searches.tar.gz::searches/openalex-measure-rigidity.json` |
| OpenAlex | <https://api.openalex.org/works?search=simultaneous%20Host%20equidistribution%20theorem&per-page=20&select=id,doi,title,publication_year,primary_location,open_access> | `bounded-searches.tar.gz::searches/openalex-simultaneous-host.json` |
| Crossref | <https://api.crossref.org/works?query.bibliographic=Furstenberg%20times%20p%20times%20q%20closed%20invariant%20set&rows=20&select=DOI,title,author,published,URL,type> | `bounded-searches.tar.gz::searches/crossref-closed-set.json` |
| Crossref | <https://api.crossref.org/works?query.bibliographic=Rudolph%20Johnson%20invariant%20measure%20entropy%20times%20p%20times%20q&rows=20&select=DOI,title,author,published,URL,type> | `bounded-searches.tar.gz::searches/crossref-measure-rigidity.json` |
| Crossref | <https://api.crossref.org/works?query.bibliographic=simultaneous%20Host%20equidistribution%20theorem&rows=20&select=DOI,title,author,published,URL,type> | `bounded-searches.tar.gz::searches/crossref-simultaneous-host.json` |

The deterministic archive contains only these six retained responses and an
internal `SEARCH_HASHES.sha256`; `reproduce.sh verify` checks every member.

One parallel Crossref request returned HTTP 429; the exact request was retried
with four retries and a two-second delay and then succeeded. The original F67
institutional scan required `curl -k` in this environment because its TLS chain
was rejected. Johnson's and Host's full publisher PDFs were subscription-only;
their publisher abstracts and DOI metadata were retained instead. These are
retrieval limitations, not evidence that other copies or other theorems do not
exist.

The bounded negative conclusion is only this: among F67, R90, J92, H95, H22,
A20, their cited references inspected during this run, and the first 20 results
of each listed query, no theorem was found that converts T37's carry identities
or `CrossBaseTransition` definition alone into T20 density for every fixed
point. No exhaustive MathSciNet, zbMATH, citation-network, book, thesis,
non-English, or post-2026-08-03 search was performed. Search failure is not an
absence theorem.

## 8. Reproduction and conclusion

From a directory containing only this artifact bundle:

```sh
chmod +x reproduce.sh
./reproduce.sh verify
./reproduce.sh extract /tmp/t44-extract
./reproduce.sh retained-searches /tmp/t44-retained-searches
./reproduce.sh search /tmp/t44-search
./reproduce.sh fetch /tmp/t44-fetch
```

`verify` checks every declared artifact against `HASHES.sha256`, unpacks the
bounded-search archive in a temporary directory, and checks every retained
response against its internal manifest. `extract` reruns `pdftotext -layout`
and checks all four generated hashes. `retained-searches` exposes and verifies
the six retained query responses. `search` repeats those queries, while `fetch`
redownloads the eight retained theorem-source and DOI-metadata endpoints and
prints fresh hashes. It does not recompile the vendored Lean interfaces.
Publisher pages, repository files, and metadata rankings can change; a fresh
mismatch records source mutation and does not invalidate the separately
retained and verified bytes.

The audit identifies three exact outcomes:

1. F67 gives a direct conditional topological route: forward `T_16` invariance
   of the decimal orbit closure, plus irrationality, implies T20 density.
2. H22 gives decimal equidistribution and A20 gives full `JMix`, but only for
   almost every point of additional positive-entropy invariant measure systems.
3. Rudolph-Johnson measure rigidity cannot start from T37 alone: the first
   absent object is a probability measure on one circle invariant under both
   multipliers. Carry compatibility, unbounded carry coordinates, and
   continuation-language complexity do not provide that object.

None of these outcomes establishes any of the excluded named-point or digit
claims in Section 1.
