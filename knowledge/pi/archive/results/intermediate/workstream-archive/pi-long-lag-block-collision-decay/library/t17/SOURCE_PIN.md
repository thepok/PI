# T17 source pin

Retrieval and audit date: 2026-07-25 UTC.

`pdftotext -layout` produced ordinary text from the retained PDF. No OCR was
used. The retained PDF is authoritative.

## Canonical statement

- Retained file: `CANONICAL_STATEMENT.txt`
- Original source URL: none; this is the local canonical question formulated
  by the system on 2026-07-23.
- SHA-256:
  `db1a5656ab93808f9729f08a2e0cae8c7612d5d3225b41ca791f5f381d90a0c3`
- Locator: lines 1-10 for C1, lines 17-35 for ambiguities and sibling
  variants, and lines 38-39 for the verification rules.

T17 constructs a sibling decimal real. It neither changes nor answers this
fixed-pi statement.

## S1: irrationality-exponent exceptional-set dimension

- Authors: Veronica Becher, Jan Reimann, and Theodore A. Slaman
- Title: *Irrationality Exponent, Hausdorff Dimension and Effectivization*
- Journal: *Monatshefte fur Mathematik* 185 (2018), 167-188
- DOI: <https://doi.org/10.1007/s00605-017-1094-2>
- Immutable record: <https://arxiv.org/abs/1601.00153v2>
- Retained PDF URL: <https://arxiv.org/pdf/1601.00153v2>
- Retained file: `becher-reimann-slaman-1601.00153v2.pdf`
- SHA-256:
  `a65fe8708116a939a29bf570f1846b234836070831a565f5bfbe4098a39050c4`
- PDF properties: 20 pages, 270994 bytes, PDF 1.4; text extraction available.

Exact locators in the retained PDF:

1. PDF page 1, first paragraph after the abstract, defines the irrationality
   exponent as the supremum of the real `z` for which
   `0 < |x-p/q| < 1/q^z` holds for infinitely many integer pairs `(p,q)` with
   `q>0`. It also records that rational numbers have exponent 1.
2. PDF page 2, first full paragraph, states that Jarnik and independently
   Besicovitch showed that the Hausdorff dimension of the set of real numbers
   whose irrationality exponent is greater than or equal to `a` is `2/a`.

The T17 note applies the second statement at `a=8`, obtaining dimension
`1/4` for the exceptional set `{x:mu(x)>=8}`. The source's literal
"greater than or equal" formulation handles the endpoint; the note does not
replace that set by the fixed-exponent limsup set.

The cited theorem is external mathematical evidence, not a kernel-checked
Lean theorem. It is the only external mathematical input to the T17 proof.

## Replay

From a directory containing only the delivered artifacts, run:

```sh
sh verify_sources.sh
```

The script checks the retained hashes and source locator text. A matching
hash proves byte identity, not the truth of the cited theorem; a reviewer must
inspect the displayed source locator as well.
