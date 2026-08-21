# T13 source pin

Retrieval and audit date: 2026-07-24 UTC.

All formulas quoted in `T13_MANY_ANCHOR_INCIDENCE.md` are transcribed in
ASCII/LaTeX.  The retained PDFs are authoritative.  `pdftotext -layout`
produced text for all three files; no OCR was used.

## Canonical statement

- Retained file: `CANONICAL_STATEMENT.txt`
- Original source URL: none; this is the local canonical question formulated
  by the system on 2026-07-23.
- SHA-256:
  `db1a5656ab93808f9729f08a2e0cae8c7612d5d3225b41ca791f5f381d90a0c3`
- Locator: lines 1-10 for C1; lines 17-35 for sibling variants, especially
  A13; lines 38-39 for verification rules.

The T13 anchor count is a sibling route and does not replace the canonical
ordered long-lag block count.

## S1: irrationality measure of pi

- Authors: Doron Zeilberger and Wadim Zudilin
- Title: *The Irrationality Measure of Pi is at most 7.103205334137...*
- Journal: *Moscow Journal of Combinatorics and Number Theory* 9 (2020),
  407-419
- DOI: <https://doi.org/10.2140/moscow.2020.9.407>
- Publisher PDF URL:
  <https://msp.org/moscow/2020/9-4/moscow-v9-n4-p06-s.pdf>
- Retained file: `zeilberger-zudilin-moscow-2020-9-407.pdf`
- SHA-256:
  `3b11c4bf3e25927227ac8f7f4e49d7f1d3efeb42beecd7f3b8c64efb162d20b5`
- PDF properties: 16 pages, 804062 bytes, PDF 1.4.

Exact locators:

1. PDF page 2 (journal page 407), Introduction, first paragraph: the paper
   defines the irrationality measure as the smallest `mu` such that, for every
   positive `epsilon`, `|x-p/q| > q^(-mu-epsilon)` for all sufficiently large
   denominators.
2. PDF page 13 (journal page 418), paragraph headed `World record`: the paper
   states that its construction implies the upper bound
   `7.10320533413700172750577342281...` for the irrationality measure of pi.

The note uses only the weaker exact terminating rational `U=7.103206`.
The publication is external mathematical evidence, not a Lean theorem.

## S2: finite-type rotation discrepancy

- Author: William D. Banks
- Title: *On certain zeta functions associated with Beatty sequences*
- Published in: *Acta Arithmetica* 185 (2018), 233-247
- Published DOI: <https://doi.org/10.4064/aa170528-29-3>
- Immutable manuscript record: <https://arxiv.org/abs/1705.09969v1>
- Retained v1 PDF URL: <https://arxiv.org/pdf/1705.09969v1>
- Retained file: `banks-2018-beatty-zeta.pdf`
- SHA-256:
  `18db9d92efa6e584bb1fbcde4bb82e451e3f5b3cfe5b206d9a4b00a36c7a5a4b`
- PDF properties: 13 pages, 213549 bytes, PDF 1.4; text extraction available.

The PDF's embedded metadata incorrectly names another Banks paper, but its
visible title page, author, arXiv identifier `1705.09969v1`, and full contents
are the retained Beatty-sequence paper.  This metadata mismatch is recorded
rather than hidden.

Exact locator: PDF page 4, Section 2.2, lines headed `Discrepancy and type`,
especially Lemma 2.1.  The source:

1. defines discrepancy as the supremum over all intervals `I` in `[0,1)`;
2. defines type by
   `tau=sup{t: liminf_(n->infinity) n^t ||n gamma||=0}`; and
3. states for every shift `delta` that
   `D_(gamma,delta)(M) << M^(-1/(tau+epsilon))`, with implied constant
   depending only on `gamma` and `epsilon`.

This exact theorem, combined with `tau(pi)<=U-1`, gives every exponent
`theta<1/(U-1)`.  The endpoint is not claimed.

## S3: exact Erdos--Turan fallback

- Authors: Christoph Aistleitner, Roswitha Hofer, and Gerhard Larcher
- Title: *On evil Kronecker sequences and lacunary trigonometric products*
- Journal: *Annales de l'Institut Fourier* 67 (2017), 637-687
- DOI: <https://doi.org/10.5802/aif.3094>
- Journal PDF URL:
  <https://aif.centre-mersenne.org/article/AIF_2017__67_2_637_0.pdf>
- Retained file: `aistleitner-hofer-larcher-2017.pdf`
- SHA-256:
  `60c37b2020bde9c3e533d592bdbc10b52354f4f702c6db01edf76741aca0cbde`
- PDF properties: 52 pages, 828567 bytes, PDF 1.6; text extraction available.

Exact locators:

1. Journal page 638: normalized star discrepancy definition.
2. Journal page 639, equation (1.1): for every positive integer `H`,

```text
D_N^* <= 1/(H+1)
         + sum_(h=1)^H (1/h) |(1/N) sum_(k=1)^N exp(2*pi*i*h*x_k)|.
```

There is no suppressed multiplicative constant in this displayed inequality.
The T13 note derives the weaker explicit-form exponent `1/nu`, including the
circle-arc factor two, directly from this formula.

## Replay

From a directory containing only the delivered artifacts:

```sh
sh verify_sources.sh
```

The script checks every retained hash, extracts each text-bearing PDF, and
checks source-specific locator strings.  A hash match establishes byte
identity, not the truth of a mathematical claim; the displayed locators must
still be inspected.
