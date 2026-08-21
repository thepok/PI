# Source-Pinned Reduction Map for pi Digits

Status: `literature-checked` for the dated, bounded source set recorded below. This is not a proof of V1 or V3, and it does not claim a complete literature review.

## Target and Scope

The immutable local target is `knowledge/pi/statements/pi-digits.txt`, SHA-256
`2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825`
([CANONICAL]).  V1 is the canonical question: every finite decimal digit
string occurs contiguously in the decimal expansion of pi.  V3 is a distinct
sibling: every infinite decimal digit sequence occurs as a not-necessarily-
contiguous subsequence.  The canonical source records V3 as equivalent to
each digit 0,...,9 occurring infinitely often ([CANONICAL], lines 25-37).

The scope here is deliberately narrower than a classification of all facts
about pi: digit extraction, a conditional normality route, a normal artificial
constant, and two post-2020 searches.  A statement below is either quoted or
a direct consequence explicitly labeled with its cited inputs.

## 1. Unconditional BBP Digit Extraction

Bailey, Borwein, and Plouffe state in their abstract: "We give algorithms for
the computation of the d-th digit of certain transcendental numbers in various
bases."  They further state that the algorithms "require virtually no memory"
and have run times that "scale nearly linearly with the order of the digit
desired" ([BBP-1997], text lines 20-25).  For pi, their Theorem 1 says, "The
following identity holds" ([BBP-1997], lines 111-116):

\[
\pi = \sum_{k=0}^{\infty}\frac{1}{16^k}
\left(\frac{4}{8k+1}-\frac{2}{8k+4}-\frac{1}{8k+5}-\frac{1}{8k+6}\right).
\]

Thus the source-pinned unconditional result relevant here is base-16
single-position digit extraction for pi, not a digit-frequency theorem
([BBP-1997], abstract and Theorem 1).  In particular, this theorem supplies
no assertion that every finite decimal block occurs, nor that any decimal digit
occurs infinitely often.  That limitation follows from the theorem's stated
subject (computing a specified digit) and is the reason it is not a resolution
of V1 or V3 ([BBP-1997], lines 20-30, 56-69).

## 2. Bailey-Crandall's Conditional Route

Bailey and Crandall define the PRNG iteration

\[
x_n=(b x_{n-1}+r_n) \bmod 1
\]

([BC-2002], lines 301-310).  Their exact Hypothesis 3.1 (called "Hypothesis
A") is:

> "If the perturbation \(r_n=p(n)/q(n)\), a nonsingular rational-polynomial
> function with \(\deg q>\deg p\geq 0\), then \((x_n)\) is either
> equidistributed or has a finite attractor."

([BC-2002], lines 312-318).

Their exact conditional consequence is Theorem 3.3:

> "(Conditional.) On Hypothesis 3.1, each of the constants
> \(\pi,\log 2,\zeta(3)\) is 2-normal."

([BC-2002], lines 302-307).  The same paper explicitly says that it is
unknown whether this hypothesis is true ([BC-2002], lines 257-260).  Therefore
this is a conditional base-2 normality route for pi, not an unconditional
normality result and not a base-10 proof of V1 or V3.

For comparison, its Theorem 3.2 is unconditional only for a separately
specified number
\(\beta=\sum_{n\geq1}r_n/b^n\) whose perturbations converge to a constant:
"Then \((x_n)\) is equidistributed (dense) iff \(\beta\) is b-normal
(b-dense)" ([BC-2002], lines 264-278).  This theorem does not identify
\(\beta\) with pi; it explains the reduction mechanism used in the conditional
statement.

## 3. Champernowne's Base-10 Template

The same source-pinned Bailey-Crandall paper records the base-10
Champernowne constant exactly as

> "the 10-normal, binary Champernowne constant [Champernowme 33]:
> \(C_{10}=0.(1)(2)(3)(4)(5)(6)(7)(8)(9)(10)(11)(12)\cdots\)"

([BC-2002], lines 72-81).  Here the parenthesized strings are concatenated,
as the paper immediately explains ([BC-2002], line 81).  This is an
unconditional normality theorem for an explicitly constructed decimal, but it
is not a theorem about pi ([BC-2002], lines 72-83).

The cited original is D. G. Champernowne, *The Construction of Decimals
Normal in the Scale of Ten*, Journal of the London Mathematical Society 8
(1933), 254-260, DOI
<https://doi.org/10.1112/jlms/s1-8.4.254> ([CHAMPER-1933-BLOCKER]).  Its source
PDF could not be retrieved in this run; the exact blocker is recorded below.
Accordingly, the quoted mathematical statement above is pinned to the
retrieved Bailey-Crandall PDF, while the original-paper citation is recorded
for follow-up rather than being represented as locally reproduced.

## 4. Post-2020 Searches and Relevant Result

Two targeted Crossref searches were performed on 2026-07-21.  They are
bounded discovery procedures, not proofs of global nonexistence of a result.

1. `normality of pi`, restricted to 2021-01-01 through 2026-07-21 and journal
   articles, returned unrelated uses of "normality" and "Pi" in its first 20
   records; no included record was a pi-digit normality result
   ([SEARCH-1]).
2. `BBP formula normality pi`, with the same date/type restriction, found the
   relevant 2021 paper below among otherwise noisy matches ([SEARCH-2]).

Barsky, Munoz, and Perez-Marco's 2021 paper is a genuine post-2020 development
about BBP formulas.  Its abstract says: "We present a general procedure to
generate infinitely many BBP and BBP-like formulas for the simplest
transcendental numbers," and specifically says it can derive the main known
BBP formulas for pi ([BMPM-2021], text lines 11-19).  Its introduction repeats
the BBP pi formula and says it permits computation of deep binary or
hexadecimal digits without computing earlier digits ([BMPM-2021], lines 26-33).
This is progress on the supply and structure of BBP formulas, not an asserted
proof of normality, decimal disjunctivity, or V3 in the cited paper.

No post-2020 source located by either bounded search is presented here as a
proof of base-10 normality of pi, V1, or V3.  This is a report about these two
search outputs only, not a claim that no such work exists anywhere
([SEARCH-1], [SEARCH-2]).

## 5. Precise Frontier for V1 and V3

**V1 (canonical).**  V1 remains open in the canonical statement ([CANONICAL],
lines 3-10 and 25-26).  The unconditional result assembled here is BBP
base-16 digit extraction ([BBP-1997]); it does not establish a universal
decimal-block occurrence assertion.  Bailey-Crandall supplies only the
conditional implication
`Hypothesis A -> pi is 2-normal` ([BC-2002], Theorem 3.3).  Even if that
conditional theorem were available unconditionally, it concerns base 2, so it
is not itself a base-10 proof of V1.  Base-10 normality would imply V1 by the
definition of normality: every finite block has positive limiting frequency
([BC-2002], lines 37-41), but no cited source proves that premise for pi.

**V3 (sibling, not a substitute for V1).**  V3 remains open in the canonical
statement ([CANONICAL], lines 34-37).  By the canonical equivalence, resolving
V3 amounts to proving that every decimal digit occurs infinitely often in pi
([CANONICAL], lines 34-37).  Neither BBP's specified hexadecimal-digit
algorithm nor the conditional base-2 theorem gives this decimal recurrence.
Base-10 normality would imply the recurrence because each one-digit block has
limiting frequency \(1/10\) ([BC-2002], lines 37-41), but this remains a
conditional route only after an additional, unproved base-10 normality premise.

**Strongest unconditional result in this reduction map.**  The strongest
directly pi-specific unconditional result pinned here is the BBP theorem and
its base-16 digit-extraction algorithm ([BBP-1997]).  The strongest
unconditional normality theorem pinned here is instead for the artificial
Champernowne constant, not pi ([BC-2002], lines 72-83).  These statements are
intentionally not conflated.

## Source Pins and Retrieval Log

### [CANONICAL]

- Local immutable source: `knowledge/pi/statements/pi-digits.txt`.
- SHA-256: `2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825`.

### [BBP-1997]

- Bailey, D. H.; Borwein, P.; Plouffe, S., *On the Rapid Computation of
  Various Polylogarithmic Constants* (NASA technical report version, 1996;
  published in *Mathematics of Computation* 66 (1997), 903-913).
- Published DOI: <https://doi.org/10.1090/S0025-5718-97-00856-9>.
- Retrieved PDF URL: <https://ntrs.nasa.gov/api/citations/19970009337/downloads/19970009337.pdf>.
- PDF SHA-256: `e4e0b97fde01328ec41da5f2cd4d6ffc8bcd2b7bd7516b9d8afc320f6d1916c4`.
- Local PDF: `sources/pdf/bbp-1997-nasa.pdf`; `pdftotext -layout` output:
  `sources/text/bbp-1997.txt`.
- Mirror failure retained for reproducibility: OpenAlex content URL
  <https://content.openalex.org/works/W2073085121.pdf> returned HTTP 401.
  The AMS URL
  <https://www.ams.org/mcom/1997-66-218/S0025-5718-97-00856-9/S0025-5718-97-00856-9.pdf>
  returned HTTP 200 but HTML rather than a PDF, so `pdftotext` rejected it.

### [BC-2002]

- Bailey, D. H.; Crandall, R. E., *Random Generators and Normal Numbers*,
  *Experimental Mathematics* 11 (2002), 527-546.
- DOI: <https://doi.org/10.1080/10586458.2002.10504704>.
- Retrieved PDF URL: <https://www.davidhbailey.com/dhbpapers/bcnormal-em.pdf>.
- PDF SHA-256: `9d1510fc72b6298295a3f10ca6d314936d083bc698982e0386e02bd8c9d9108f`.
- Local PDF: `sources/pdf/bailey-crandall-2002-alt.pdf`; `pdftotext -layout`
  output: `sources/text/bailey-crandall-2002-alt.txt`.
- Failed mirror: <https://content.openalex.org/works/W2145880011.pdf> returned
  HTTP 401.

### [BMPM-2021]

- Barsky, D.; Munoz, V.; Perez-Marco, R., *On the genesis of BBP formulas*,
  *Acta Arithmetica* 198 (2021), 401-426.
- DOI: <https://doi.org/10.4064/aa200619-28-9>; accessible preprint:
  <https://arxiv.org/abs/1906.09629>.
- Retrieved PDF URL: <https://export.arxiv.org/pdf/1906.09629>.
- PDF SHA-256: `64629d2323ad8e1a11b457b3572c1568993c29b37e3959e8e9d31fa03d06fa2f`.
- Local PDF: `sources/pdf/barsky-munoz-perez-marco-2021.pdf`; `pdftotext
  -layout` output: `sources/text/barsky-munoz-perez-marco-2021.txt`.

### [CHAMPER-1933-BLOCKER]

- Champernowne, D. G., *The Construction of Decimals Normal in the Scale of
  Ten*, *Journal of the London Mathematical Society* s1-8 (1933), 254-260.
- DOI: <https://doi.org/10.1112/jlms/s1-8.4.254>.
- Publisher text-mining URL
  <https://api.wiley.com/onlinelibrary/tdm/v1/articles/10.1112%2Fjlms%2Fs1-8.4.254>
  returned HTTP 400 with the descriptive User-Agent used for this survey.
- Wiley full-PDF URL
  <https://onlinelibrary.wiley.com/wol1/doi/10.1112/jlms/s1-8.4.254/fullpdf>
  returned HTTP 403.  No PDF SHA-256 is claimed for this source.

### [SEARCH-1]

- Query URL: <https://api.crossref.org/works?query.title=normality%20of%20pi&filter=from-pub-date:2021-01-01,until-pub-date:2026-07-21,type:journal-article&rows=20&select=DOI,title,author,published,URL,type>.
- Retrieved 2026-07-21; response SHA-256:
  `77d25ef0aaa0e83f5655cc45b35cc60b9ab0b6d3702c2270d253645651cbd8e4`.
- Local response: `sources/search-1-crossref-normality-pi.json`.

### [SEARCH-2]

- Query URL: <https://api.crossref.org/works?query.bibliographic=BBP%20formula%20normality%20pi&filter=from-pub-date:2021-01-01,until-pub-date:2026-07-21,type:journal-article&rows=20&select=DOI,title,author,published,URL,type>.
- Retrieved 2026-07-21; response SHA-256:
  `700699c3db2d56ac5ee582ef34c83dfa139d9c885bc775d2ae2923554b5390f3`.
- Local response: `sources/search-2-crossref-bbp-normality-pi.json`.
