# T19: Post-Frontier Separation Audit for Decimal Digits of Pi

Status: `literature-checked` for the explicitly bounded searches and five
retrieved primary sources dated 2026-07-21. This is not an exhaustive survey.
Search failure is not evidence of absence. This audit does not resolve
canonical V1 or sibling V3.

## 1. Immutable target and quantifiers

The canonical source is `knowledge/pi/statements/pi-digits.txt`, SHA-256
`2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825`.
It distinguishes:

- **V1 (canonical):** for every finite word over `{0,...,9}`, there exists a
  position at which that word occurs contiguously in the floor-based decimal
  expansion of pi.
- **V3 (sibling):** for every infinite word over `{0,...,9}`, there is a
  strictly increasing sequence of positions embedding it in the decimal
  expansion of pi. By accepted T9, this is equivalent to: for every digit
  `a in {0,...,9}` and every bound `B`, there is a position `i >= B` with
  digit `a`.

The original wording also admitted V2, concerning infinite contiguous tails.
T19 concerns only V1 and V3. It does not use finite computation as evidence
for either universal statement.

In this audit, "post-T18" means an audit performed after, and separated from,
the accepted T11/T13/T14/T16/T18 frontier. It is not a publication-date
restriction. "Novel over T11/..." means logical information not already in
those accepted program artifacts; it is not a claim of historical novelty.

## 2. Accepted comparison frontier

The comparison files were hashed again in the staged knowledge library.

| Item | Exact comparison fact | Staged SHA-256 |
|---|---|---|
| T11 | For every `n > 0`, the decimal factor complexity of pi satisfies `p_pi(n) >= n+1`. It does not approach the `10^n` assertion needed for V1. | `c6f4a9625b74bcd32ce475029d1ac365ab426aa385483f381f42571ffe3e3b42` |
| T13 | At least two unspecified distinct decimal digits occur arbitrarily late in pi. | `67a6cc5c37e94f3b305566c80c438ab77971fcc9c1bd0fa5f60f1ef81d55d5ec` |
| T14 | `C_pi(N) >= (log N)/(log 8) - C14` for every `N >= 1`, where `C_pi` counts adjacent digit changes. This is an accepted, source-pinned `proof sketch`, not a Lean theorem. | `431945bf7251d6b31eccaee474d21d80df968e5a5c492304455e6cdf3ea423e2` |
| T16 | A decimal Thue-Morse countermodel shows that the generic package of linear complexity, recurrent digits, strong digit-change growth, and irrationality information does not imply decimal disjunctivity. It is not a fact about pi. | `5a4509e1ed49cea2561d87fbd19d739fe8d6a48547607b2ea1ec0de815f77f72` |
| T18 | There are fixed unequal digits `a,b` such that, on unbounded prefix lengths, occurrences of `a`, occurrences of `b`, and occurrences of the directed bigram `ab` all have a logarithmic lower bound derived from T14. This is partial V3 information, not V3. | `c0f2a01e4bc5b2510e88ec4735128acffe591174a685b67c5e7f0401569cbf83` |

T6 already audits BBP hexadecimal digit extraction and Bailey--Crandall's
conditional base-2 dynamical route. T12 already refutes unrestricted transfer
from base-2 normality to decimal normality or decimal disjunctivity. Those
surveys are cited here and not repeated.

## 3. Candidate-by-candidate separation table

`None` in a novelty cell means no new theorem about the decimal digit stream
of pi relative to that item. It does not mean that the source has no
mathematical content.

| Candidate | Category | Radix | Status for pi | Novel over T11 | Novel over T13 | Novel over T14 | Novel over T16 | Novel over T18 | Exact V1 relevance | Exact V3 relevance |
|---|---|---|---|---|---|---|---|---|---|---|
| Stoneham 1983, Theorem 5 | Pi/4-specific rational-approximant mechanism and finite-word occurrence in approximants | `g=2^alpha p^beta`; base 10 at `alpha=beta=1,p=5` | Unconditional for a subsequence of rational Wallis approximants; no theorem transfers the asserted blocks to pi/4 or pi | None: no `p_pi(n)` bound | None: no recurrent pi digit | None: no pi change count | Does not evade T16 because it establishes no invariant of pi | None: no fixed pi digit or bigram | No V1 consequence. The paper explicitly identifies the missing stable-portion step. | No V3 consequence; rational periodic approximants say nothing about arbitrarily late pi digits. |
| Barral--Loiseau 2011, Theorem 4.1 plus Conjecture 4.1 | Pi-specific large-deviation/dynamical hypothesis | Every integer base `m>=2`, including 10 | The implication `(P) -> normality` is proved; `(P)` for pi is explicitly conjectural | **Conditional only:** at `m=10`, `(P)` gives normality and hence `p_pi(n)=10^n`; unconditionally none | **Conditional only:** every digit then has frequency `1/10`; unconditionally none | **Conditional only:** much stronger positive frequencies; unconditionally none | `(P)` is pi-specific structure that would bypass T16's generic countermodel, but the needed premise is unproved | **Conditional only:** all directed blocks have positive frequency; unconditionally none | Base-10 `(P)` implies normality, hence V1. The hypothesis is not proved for pi. | Base-10 `(P)` implies every digit has frequency `1/10`, hence V3. The hypothesis is not proved for pi. |
| Borwein--Borwein--Galway 2004, Theorem 7 | Exclusion of a defined individual-digit formula class | Integer `b>2` that is not a proper power; in particular base 10 | Unconditional negative theorem about pi, but only for Q-linear Machin-type BBP arctangent formulas | New mechanism-level exclusion, but no complexity information | None | None | It narrows one pi-specific mechanism class; it proves no digit invariant and does not by itself evade or strengthen T16 | None | No implication for V1. Excluding one formula class neither proves nor refutes disjunctivity. | No implication for V3. |
| Almkvist--Krattenthaler--Petersson 2003, p. 1 | Published attestation of Bellard's nonsequential decimal random-access algorithm | Decimal | Unconditional algorithmic assertion in the paper, but the algorithm is delegated to Bellard's webpage/code rather than stated as a numbered theorem | None: computability of a requested finite position gives no lower bound on distinct words | None | None | Random access is not a combinatorial invariant and does not overcome T16 | None | No V1 implication; a procedure for supplied finite indices does not prove that a desired block has an index. | No V3 implication; it does not prove any digit recurs. |
| Aretxabaleta et al. 2020, equations (1), (13), and Section 6.3 | Pi-specific Galperin-billiards collision-count mechanism | Decimal `b=10` (the paper also discusses other bases) | Exact ideal-model collision formula away from stated degeneracies; identifying it with every decimal prefix uses an approximation and systematic-error analysis, not a proved universal-`N` theorem | None: the mechanism gives no asymptotic distinct-word bound | None | None | New pi-specific mechanism, but it establishes no combinatorial invariant that evades T16 | None | No V1 implication; even a certified algorithm for each supplied prefix would not prove that every word occurs. | No V3 implication; it proves no digit occurs arbitrarily late. |

The only information in this table not already represented by the accepted
digit-combinatorics frontier is mechanism-level:

1. Barral--Loiseau provide a precise, non-tautological but unproved
   pi-specific hypothesis `(P)` that would imply base-10 normality.
2. Borwein--Borwein--Galway unconditionally exclude one precisely defined
   decimal BBP/Machin formula class for pi.
3. Almkvist et al. publish an attestation of nonsequential decimal digit
   access, but no occurrence theorem follows.
4. Aretxabaleta et al. give a base-10-compatible dynamical collision
   mechanism and analyze its prefix approximation, but do not prove the
   decimal-prefix identity for every `N` or any occurrence theorem.

None is an unconditional extension of V1 or V3.

## 4. Exact source statements and pins

### S1. Stoneham: normal rational approximants, not stable pi digits

R. G. Stoneham, *On a sequence of (j, epsilon)-normal approximations to
pi/4 and the Brouwer conjecture*, Acta Arithmetica 42(3) (1983), 265--279.

- DOI: <https://doi.org/10.4064/aa-42-3-265-279>
- Stable record: <https://eudml.org/doc/205875>
- Retrieved PDF: <https://www.impan.pl/shop/publication/transaction/download/product/103744?download.pdf>
- PDF SHA-256: `9acc206574c7826dfc901498066bfc9df9763ba21ea737e9b1731a4581ffd095`
- Local file: `stoneham-1983-pi-approximations.pdf`

The PDF is an eight-image scan containing two printed pages per physical
page. `pdftotext -layout` (Poppler 22.12.0) produced only eight form-feed
characters; its retained output has SHA-256
`a61f149fa51d21a7666743f05977a61c858db20e63ecc70834dd3885b3062550`.
Consequently the rendered PDF, physical page 7, is authoritative for the
following exact transcriptions. Mathematical glyphs are rendered in Markdown
and line wrapping is normalized.

**Theorem 5, printed p. 276:**

> "There exists an infinite sequences of positive integers n such that the
> associated partial Wallis infinite products
> `p_n/q_n = product_(i=1)^n (1-1/(2i+1)^2)` are `(j, epsilon)`-normal and
> purely periodic in base `g = 2^alpha p^beta` where `p` is any fixed odd
> prime."

Setting `alpha=beta=1` and `p=5` makes `g=10`; the theorem is therefore
genuinely decimal. Its subject is nevertheless the rational sequence
`p_n/q_n`, not the decimal expansion of pi.

**The paper's limitation, printed p. 277:**

> "Unfortunately, at the present time, we cannot say whether the block
> 0123456789 is in the 'stable' portion of the approximation to pi/4, i.e. the
> part of the period which does not change as n increases, or the portion of
> the period which changes as n increases without bound."

Thus even the displayed ten-digit word is not proved to survive in the limit.
Failure of this route in the cited paper is not proof that no stable-prefix
argument can exist.

### S2. Barral--Loiseau: a precise conditional route

Julien Barral and Patrick Loiseau, *Large deviations for the local
fluctuations of random walks*, Stochastic Processes and their Applications
121 (2011), 2272--2302. The retained author version adds the subtitle
*and new insights into the "randomness" of Pi*.

- DOI: <https://doi.org/10.1016/j.spa.2011.06.004>
- Accessible author version: <https://arxiv.org/abs/1004.3713>
- Retrieved PDF: <https://export.arxiv.org/pdf/1004.3713>
- PDF SHA-256: `71bb0f4cfd41a6a315f7be3e1f0c927ec880794bc4cc059ce385dbe8cfbd6735`
- `pdftotext -layout` SHA-256:
  `eb7b9b3fbe896dabf42f38a320fb73c327f6d061c5b56b266978730ecacb6246`

Using the measures and rate function defined in its equations immediately
above, the paper states (author version, printed p. 18; extracted lines
956--964; formula typography normalized):

> "Property (P): The sequence `(mu_n^D)_(n>=1)` obeys in `R^d` the same LDP
> with rate `I` as that provided by Theorem 3.3 for `(mu_n^t)_(n>=1)` (for
> `nu_psi`-almost every `t`). and"

The dangling word "and" is printed in the source immediately before Theorem
4.1; it is preserved here rather than silently repaired.

The exact consequence is (the same printed page; extracted lines 964--968):

> "Theorem 4.1. Property (P) implies the normality of
> `sum_(i>=1) D_i m^(-i)` in basis m."

The exact pi premise is explicitly not a theorem (printed p. 19; extracted
lines 1006--1009):

> "Conjecture 4.1. For every integer m >= 2, the digits of the fractional part
> of either Pi or the Euler constant in basis m satisfy (P)."

At `m=10`, the theorem plus this conjecture would imply base-10 normality,
hence V1 and V3. Numerical support later in the paper does not discharge the
conjecture. This is the clearest natural hypothesis found for a next proof
item, but it is not unconditional progress.

### S3. Borwein--Borwein--Galway: a decimal formula-class exclusion

Jonathan M. Borwein, David Borwein, and William F. Galway, *Finding and
Excluding b-ary Machin-Type Individual Digit Formulae*, Canadian Journal of
Mathematics 56(5) (2004), 897--925.

- DOI: <https://doi.org/10.4153/CJM-2004-041-2>
- Retrieved published PDF:
  <https://www.cambridge.org/core/services/aop-cambridge-core/content/view/BB7919C8E1AE66878AE8D7BC7F0EBFA3/S0008414X0003385Xa.pdf/div-class-title-finding-and-excluding-span-class-italic-b-span-ary-machin-type-individual-digit-formulae-div.pdf>
- PDF SHA-256: `51d47633a37a9d4b024ccabfd782fe0d0ade85f554a8a6fc3fe2773832ecc2cb`
- `pdftotext -layout` SHA-256:
  `a29b85486b00149ee954c34cacba8531e939483161c3205e26ce27dc9000e412`

The exact theorem is on printed p. 918 (extracted lines 1171--1172):

> "Theorem 7 Given b > 2 and not a proper power, there is no Q-linear b-ary
> Machin-type BBP arctangent formula for pi."

The integer 10 is not a proper power: its prime exponents are both 1. Theorem
7 therefore excludes this formula class in radix 10. The scope qualifiers are
essential: it does not exclude all BBP-type formulas, all random-access
algorithms, or all decimal digit-extraction mechanisms. It is a rigorous
negative reduction result, not a digit-occurrence theorem.

### S4. Almkvist--Krattenthaler--Petersson: published random-access attestation

Gert Almkvist, Christian Krattenthaler, and Joakim Petersson, *Some New
Formulas for Pi*, Experimental Mathematics 12(4) (2003), 441--456.

- DOI: <https://doi.org/10.1080/10586458.2003.10504512>
- Accessible preprint: <https://arxiv.org/abs/math/0110238>
- Retrieved PDF: <https://export.arxiv.org/pdf/math/0110238>
- PDF SHA-256: `a1d194272367e015aa6a39499405f2ebd398b7c032e3d893bc8cf3d2fee2476d`
- `pdftotext -layout` SHA-256:
  `6efa67c934e33ca378948d0db40ee9ecc6d9e6750236fd815ef582df202edd9c`

The exact statement in the opening paragraph (preprint p. 1; extracted lines
36--38; journal p. 441) is:

> "Fabrice Bellard [1, file pi1.c] found an algorithm for computing the n-th
> decimal of pi without computing the earlier ones. Thus he improved an
> earlier algorithm due to Simon Plouffe [6]."

This is not a numbered theorem, and reference [1] delegates the actual
algorithm to Bellard's pi webpage. The published paper proves formulas used by
the method, but does not turn finite random access into a statement about
which values occur. T19 includes it because it is nonsequential and therefore
not excluded as an ordinary spigot; it supplies no information relevant to
V1 or V3.

### S5. Aretxabaleta et al.: an idealized collision mechanism

X. M. Aretxabaleta, M. Gonchenko, N. L. Harshman, S. G. Jackson,
M. Olshanii, and G. E. Astrakharchik, *The Dynamics of Digits: Calculating Pi
with Galperin's Billiards*, Mathematics 8(4) (2020), article 509.

- DOI: <https://doi.org/10.3390/math8040509>
- Accessible author version: <https://arxiv.org/abs/1712.06698v3>
- Retrieved PDF: <https://export.arxiv.org/pdf/1712.06698v3>
- PDF SHA-256: `67dc1abf078862203cfd4b7becd2ea40ec486196cde26e3431473ae0202fddca`
- `pdftotext -layout` SHA-256:
  `8fc120062e5d861b6f064c47ce56270aa2f9c20a26e79aefefd139ebb140fdd4`

The paper parameterizes its ideal elastic two-ball-and-wall system by
(equation (1), extracted lines 188--193)

```text
M/m = b^(2N),
```

calling `b` the base and `N` the mantissa. Its exact collision-count formula
is (equation (13), extracted lines 422--430; `int` means integer part)

```text
Pi(b,N) = int[pi / arctan(b^(-N))].
```

The exact radix interpretation stated in Section 6 (printed p. 20; extracted
lines 1251--1256) is:

> "Equation (13) has a profound mathematical meaning, as the number of
> collisions Pi(b, N) provides the first N digits of the fractional part
> (i.e., digits beyond the radix point) of the number pi in base b."

For decimal, Section 6.3 states (printed p. 21; extracted lines 1296--1304):

> "For the most natural case of the decimal base system, b = 10, the number
> of collisions Pi(10, N) is given in Table 1. ... One can see that the
> billiard method correctly approximates the number pi as 3 plus N more
> digits in the decimal base."

The first quotation is the paper's interpretation of its collision formula;
the second retains the paper's more cautious word "approximates". Section 6.2
excludes the degenerate `N=0` case and immediately records a further
degeneracy when the billiard angle is a submultiple of pi. More importantly,
the digit identification replaces `arctan(b^(-N))` by `b^(-N)` in equation
(14). Sections 5--6 analyze the possible difference as a systematic error,
using Figure 13 and finite tables.

Accordingly, this audit accepts the ideal collision formula, with the source's
degeneracy qualifications, but does **not** promote the decimal-prefix
interpretation to a theorem valid for every `N`. It classifies the paper as a
pi-specific dynamical mechanism for approximating finite prefixes. It is not
random access, a frequency theorem, or a proof that any specified block
occurs. Physical realizability, finite entries in Table 1, and the paper's
systematic-error plots are not treated as V1/V3 evidence here.

## 5. Bounded searches and negative classifications

The retained bundle run started at `2026-07-21T17:22:25Z`; its requests
completed immediately thereafter. The timestamp is a run-start marker, not a
claim that all fifteen HTTP requests occurred in the same second. Exact URLs,
parameters, and complete responses are in the three JSON bundles and in
`reproduce-t19.sh`.

| Database | Fixed query families | Bound per query | Returned before deduplication | Retained file and SHA-256 |
|---|---|---:|---:|---|
| Crossref | `pi decimal digit occurrence`; `pi decimal recurrence nonzero digits`; `pi factor complexity decimal expansion`; `pi nth decimal digit algorithm`; `pi normality dynamical system` | first 20 selected metadata records | 100 | `search-crossref.json`, `3442012b9ec811219e8e8e6669df52075400fadc9a082b53df92c56079fea1c3` |
| OpenAlex | The same five phrase searches | first 25 selected metadata records | 125 | `search-openalex.json`, `be65add65f680c3f9973235cdefa84a07f722f744d4a1da5f992cf0b2963a004` |
| arXiv API | exact phrases `digits of pi`, `normality of pi`, `factor complexity AND pi`, `non-zero digits AND pi`, `nth decimal digit AND pi` | first 50 records | 11, 2, 0, 0, 0 respectively | `search-arxiv.json`, `63d9d43548b7b1fe5d0c346256b6bbe889492f0ec33ebfd9a240f43cf14e5823` |

The candidate set was formed by inspecting titles and available metadata from
these finite outputs, following DOI and reference links, and then checking the
five retained primary PDFs. The broad API rankings were noisy: many uses of
"PI" meant a controller, protein, or mathematical notation unrelated to the
constant. Ordinary sequential spigot and conventional prefix-generation
algorithms were excluded by scope; the Galperin source was retained because it
is a pi-specific dynamical encoding rather than an ordinary spigot. Finite
statistical studies were classified as `experiment` and were not used as
theorem evidence. T6's BBP/Bailey--Crandall sources and T12's base-transfer
sources were recognized but not duplicated.

Within only these retained bounds:

| Requested route | Bounded result |
|---|---|
| Unconditional occurrence of specified decimal digits or words in pi | No inspected primary theorem candidate extended T18. Stoneham's words occur in rational approximants, with stable transfer explicitly unresolved. |
| Unconditional distinct-word or factor-complexity growth for pi | No inspected primary theorem candidate improved T11. Returned algebraic-complexity hits require irrational algebraic input and cannot be instantiated at transcendental pi. |
| Unconditional lower bound for nonzero decimal digits of pi | No primary theorem candidate was located in the returned records. This is a bounded negative result, not an absence theorem. T13/T18 already imply recurrence/counting for unspecified distinct digits, at least one of which is nonzero. |
| Unconditional recurrence of every named decimal digit of pi | No primary theorem candidate was located in the returned records. This does not prove that no such publication exists. |
| Pi-specific radix-10 dynamical reduction | Barral--Loiseau supply `(P) -> normality`, but `(P)` for pi is their explicit conjecture. Aretxabaleta et al. give an exact ideal-billiard collision formula and an analyzed decimal-prefix approximation, not a universal-`N` prefix theorem or an occurrence result. |
| Pi-specific radix-10 digit extraction | Almkvist et al. attest nonsequential decimal access; Borwein--Borwein--Galway exclude one decimal Machin-type BBP class. Neither yields occurrence or recurrence. |

These statements describe this finite search procedure only. In particular,
zero arXiv returns and failure to promote a Crossref/OpenAlex record do not
prove global nonexistence.

## 6. Reproduction and trust boundary

From this artifact directory:

```sh
./reproduce-t19.sh verify
./reproduce-t19.sh fetch /tmp/t19-reproduction
```

`verify` checks every staged artifact hash against `HASHES.sha256`. `fetch`
downloads the five PDFs, runs `pdftotext -layout`, and replays all fifteen API
queries into three bundles. PDF and API servers are external and mutable:

- a byte-identical PDF redownload reproduces the pinned PDF hash;
- a changed publisher file is a detectable source-version change, not a
  reason to alter the retained pin;
- fresh API responses may differ as indexes change, so reproduction of a
  bounded search means replaying the exact dated query and bound. The retained
  JSON hash authenticates the response actually inspected on 2026-07-21.

The Stoneham scan is the one extraction exception: Poppler returns only page
breaks. The exact quotations must be checked against rendered printed pp.
276--277 (physical PDF page 7), as documented above.

No Lean theorem is claimed in T19. No finite computation is assigned proof
value. The outcome is a separation audit: the searched decimal routes do not
unconditionally extend the accepted V1/V3 frontier. It does not resolve V1 or
V3 and does not prove that an unsearched route or source is absent.
