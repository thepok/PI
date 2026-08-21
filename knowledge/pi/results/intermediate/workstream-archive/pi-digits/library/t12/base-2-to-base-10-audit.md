# T12: Bailey-Crandall Base-Mismatch Audit

Status: `literature-checked` for the bounded search and retrieved sources dated
2026-07-21. This audit concerns implications between properties of arbitrary
real numbers. It proves nothing about the digits of pi.

## Scope and normalized statements

The immutable canonical question is whether every finite decimal digit string
occurs contiguously in the decimal expansion of pi (`knowledge/pi/statements/pi-digits.txt`,
SHA-256
`2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825`).
That property is base-10 disjunctivity. It is weaker than base-10 normality.

For this audit, the two universally quantified implications are:

1. For every real number `x`, if `x` is normal in base 2, then `x` is normal
   in base 10.
2. For every real number `x`, if `x` is normal in base 2, then every finite
   decimal block occurs in the decimal expansion of `x`.

Schmidt defines normality by requiring every digit block to occur with its
proper frequency ([SCHMIDT-1960], p. 661, extracted text lines 17-31). Thus
base-10 normality implies base-10 disjunctivity, but failure of base-10
normality alone does not imply failure of base-10 disjunctivity. The second row
below is therefore supported by the stronger deleted-decimal-digit
construction, not merely by Schmidt's statement that a number is not simply
normal in base 10.

## Two-row implication table

| Implication | Bounded-search classification | Exact supporting quotation and source pin | Why the quotation settles this row |
|---|---|---|---|
| Base-2 normality implies base-10 normality | **refuted** | [SCHMIDT-1960], Theorem 1B, p. 661; quotations Q1 and Q2 below; DOI <https://doi.org/10.2140/pjm.1960.10.661>; retrieved PDF SHA-256 `28f1f9604d4000ada9cf9485c2d68532348065087c6bdc42a4dda982bddeea67` | Schmidt's relation `r ~ s` means that positive powers of `r` and `s` coincide. No positive powers of 2 and 10 coincide, by unique prime factorization. Theorem 1B with `r = 2`, `s = 10` gives continuum many numbers normal to base 2 but not even simply normal to base 10. |
| Base-2 normality implies base-10 disjunctivity | **refuted** | [SCHMIDT-1960], definition of `T_(s,t)` on p. 661 and Theorem 2 with its stated consequence on p. 662; quotations Q3-Q5 below; DOI <https://doi.org/10.2140/pjm.1960.10.661>; retrieved PDF SHA-256 `28f1f9604d4000ada9cf9485c2d68532348065087c6bdc42a4dda982bddeea67` | Set `r = 2`, `s = 10`, and `t = 2`. The map `T_(10,2)` reads a binary expansion and uses the same digits as a decimal expansion, so every displayed decimal digit is `0` or `1`; in particular the decimal block `2` never occurs. Schmidt's stated consequence of Theorem 2 says that `T_(10,2)(xi)` is normal to base 2 for almost every `xi`. Hence such counterexamples exist and are not base-10 disjunctive. |

Both classifications are `refuted`, in the sense that the universally
quantified implication has a counterexample. They do not assert that a
particular named constant is a counterexample.

## Exact quotations

The PDF uses `r ~ s` for multiplicative dependence and the negated relation
`r !~ s` for multiplicative independence. The plain-text extraction does not
preserve several mathematical glyphs reliably. The quotations below are exact
content transcriptions from the rendered PDF: words, punctuation, and formula
content are preserved, while line wrapping is normalized and mathematical
glyphs are rendered with the ASCII tokens `xi`, `alpha_1`, `<=`, `>=`, and
`!~`. Page and extracted-text line locations make every transcription
inspectable.

**Q1: definition of the base relation.**

> "We write r ~ s, if there exist integers n, m with r^n = s^m. Otherwise,
> we put r !~ s."

([SCHMIDT-1960], p. 661; `schmidt-1960-on-normal-numbers.txt`, lines 32-33.)

**Q2: counterexamples to normality transfer.**

> "B If r !~ s, then the set of numbers xi which are normal to base
> r but not even simply normal to base s has the power of the continuum."

([SCHMIDT-1960], Theorem 1B, p. 661; extracted text lines 38-41.)

**Q3: the digit-preserving map.**

> "Write T_(s,t), where 1 < t < s, for the following mapping in U: If
> xi = 0.a_1 a_2 ... in the scale of t, then T_(s,t) xi = 0.a_1 a_2 ...
> in the scale of s."

([SCHMIDT-1960], p. 661; extracted text lines 56-57.)

**Q4: hypothesis of the construction theorem.**

> "THEOREM 2. Assume r !~ s. Then there exists a constant alpha_1 =
> alpha_1(r, s, t) > 0 such that for almost every xi there exists a N_0(xi)
> with R_N(T_(s,t) xi, r, I) <= N^(1-alpha_1) for every N >= N_0(xi)
> and any I."

([SCHMIDT-1960], Theorem 2 and displayed formula (2), p. 662; extracted text
lines 66-70.)

**Q5: the author's explicit normality conclusion.**

> "Thus T_(s,t) xi is normal to base r for almost all xi. Since T_(s,t) xi
> is not simply normal to base s part B of Theorem 1 follows."

([SCHMIDT-1960], p. 662; extracted text lines 71-74.)

For row 2, Q3 shows that `T_(10,2)(xi)` has a decimal expansion over the
alphabet `{0,1}`, while Q4-Q5 show that almost every such image is normal to
base 2. A base-2 normal number is irrational, so this displayed decimal
expansion is not one of the two expansions of a terminating rational and is
the unique decimal expansion. The one-symbol decimal block `2` is absent,
which is an explicit failure of base-10 disjunctivity. This is strictly
stronger than the insufficient observation that the image is not base-10
normal.

## Consequence for the Bailey-Crandall route

The accepted T6 reduction map pins Bailey-Crandall's conditional theorem only
as

`Hypothesis 3.1 -> pi is 2-normal`.

The two refuted general implications show that base-2 normality, by itself,
cannot be transferred to either base-10 normality or canonical decimal V1
(base-10 disjunctivity). This does not show that pi fails either decimal
property. It only identifies an additional theorem about pi, or some
pi-specific structure connecting the bases, that the Bailey-Crandall route
would need before it could establish decimal V1.

## Source pins and reproduction

### [SCHMIDT-1960]

- Wolfgang M. Schmidt, *On Normal Numbers*, Pacific Journal of Mathematics
  10(2) (1960), 661-672.
- DOI: <https://doi.org/10.2140/pjm.1960.10.661>.
- Stable publisher PDF URL:
  <https://msp.org/pjm/1960/10-2/pjm-v10-n2-p22-s.pdf>.
- Retrieved 2026-07-21 as `schmidt-1960-on-normal-numbers.pdf`.
- PDF SHA-256:
  `28f1f9604d4000ada9cf9485c2d68532348065087c6bdc42a4dda982bddeea67`.
- `pdftotext -layout` output: `schmidt-1960-on-normal-numbers.txt`.
- Extracted-text SHA-256:
  `6c1a682f0120c1637402668b2e684e2f92b31fa2635471e2cf8b71c37bfdbc2c`.

Reproduction commands, run from the artifact directory:

```sh
curl -fL "https://msp.org/pjm/1960/10-2/pjm-v10-n2-p22-s.pdf" \
  -o "schmidt-1960-on-normal-numbers.pdf"
pdftotext -layout "schmidt-1960-on-normal-numbers.pdf" \
  "schmidt-1960-on-normal-numbers.txt"
sha256sum "schmidt-1960-on-normal-numbers.pdf" \
  "schmidt-1960-on-normal-numbers.txt"
```

## Bounded search log

The search was performed on 2026-07-21. API result sets are discovery aids,
not evidence that the literature contains no other result.

| Query or inspected source | Retrieved record | Result used in this audit |
|---|---|---|
| Crossref API: `query.bibliographic=normal numbers different bases Schmidt`, `rows=10`, selecting DOI/title/author/date/URL/type | `search-crossref-different-bases.json`, SHA-256 `2429a9abce6b9b9e5617537f4011f06783d968ea605033d884a3581e5cf27e0a` | Located Schmidt's DOI and theorem. Exact query URL is recorded below. |
| OpenAlex API full-text search: `"normal numbers" Cantor measure`, `per-page=25` | `search-openalex-cantor-measure.json`, SHA-256 `f1d521e67c83cf158203e2a6126628f5ce75d57186fc7b54080000efc9465d6b` | Located Schmidt and the modern Hochman-Shmerkin corroborating source. Exact query URL is recorded below. |
| Michael Hochman and Pablo Shmerkin, *Equidistribution from Fractal Measures*, Invent. Math. 202 (2015), DOI <https://doi.org/10.1007/s00222-014-0573-5> | `hochman-shmerkin-2015-arxiv-v3.pdf`, arXiv v3 URL <https://arxiv.org/pdf/1302.5792v3>, SHA-256 `c8689135c75e79eb19e794be96d3062eac9ca43eb05d2c95d756175e25c11101`; extracted text SHA-256 `deeedeb17ccdaa9869c4116d3869b11f66c28bb34954a21466ce187a93a8369c` | Inspected as modern corroboration. Its introduction, extracted lines 38-51, explicitly attributes the Cantor-measure normality result to Cassels and Schmidt. The primary classification above is pinned to Schmidt's original paper. |
| Accepted T6 source `knowledge_library/t6/reduction-map.md`, SHA-256 `bd95aa34c512ea934801d9baa2d574854ecbb4dc7575670fc4d8304637928f33` | Existing accepted library artifact; not duplicated | Confirmed that the unresolved Bailey-Crandall output is conditional base-2 normality of pi, not a base-10 theorem. |

Exact API URLs:

- <https://api.crossref.org/works?query.bibliographic=normal%20numbers%20different%20bases%20Schmidt&rows=10&select=DOI,title,author,published,URL,type>
- <https://api.openalex.org/works?search=%22normal%20numbers%22%20Cantor%20measure&per-page=25&select=id,doi,title,publication_year,primary_location,open_access>

All source retrievals used for the two classifications succeeded.
General-purpose web-search attempts were blocked by an automated-user
challenge, so no claim of an exhaustive web search is made. The classifications
rely on the retrieved primary paper, not on search snippets.

The Crossref and OpenAlex query responses are mutable discovery records. A
fresh adversarial replay on 2026-07-21 returned valid JSON with changed response
hashes, while the locally retained responses above preserve exactly what was
inspected during the bounded search. Neither API response is used as theorem
evidence. In the same replay, a fresh publisher-PDF download and fresh
`pdftotext -layout` conversion were byte-for-byte identical to the pinned PDF
and text hashes above; the DOI landing page again identified Schmidt, the
title, journal, volume, pages, and year.

## Audit conclusion

The bounded search classifies both universal implications as **refuted**.
Schmidt's theorem supplies base-2-normal/base-10-non-normal numbers, and its
digit-preserving Cantor construction supplies the stronger base-2-normal
numbers whose decimal expansion omits the block `2`. Therefore a conditional
proof that pi is normal in base 2 cannot, without additional pi-specific
input, be represented as progress proving decimal normality or decimal V1.
