# T4 source pin: irrationality measure of pi below 8

## Canonical problem

- File: `knowledge/pi/statements/pi-long-lag-block-collision-decay.txt`
- SHA-256: `db1a5656ab93808f9729f08a2e0cae8c7612d5d3225b41ca791f5f381d90a0c3`
- Target status: canonical A1 remains open. This artifact uses the sibling A12
  residual-pair reduction conditionally and does not prove or refute A1/C1.

## Retained publication

- Authors: Doron Zeilberger and Wadim Zudilin
- Title: *The Irrationality Measure of Pi is at most 7.103205334137...*
- Journal: *Moscow Journal of Combinatorics and Number Theory* 9 (2020),
  407-419
- Published DOI: <https://doi.org/10.2140/moscow.2020.9.407>
- Publisher article page: <https://doi.org/10.2140/moscow.2020.9.407>
- Pinned publisher PDF:
  <https://msp.org/moscow/2020/9-4/moscow-v9-n4-p06-s.pdf>
- Retained file: `zeilberger-zudilin-moscow-2020-9-407.pdf`
- Retained-file SHA-256:
  `3b11c4bf3e25927227ac8f7f4e49d7f1d3efeb42beecd7f3b8c64efb162d20b5`
- Retrieved: 2026-07-24 UTC
- PDF properties: 16 pages, 804062 bytes, PDF 1.4

The retained file is the journal publisher's screen PDF, not an unversioned
third-party copy. The article records that its Lemma 2 was corrected before
publication (journal page 408).

## Exact locators

PDF page 3 (journal page 407), Introduction, first paragraph, lines 27-34 in a
`pdftotext -layout` extraction:

> we define (see [Weisstein 2019]) the irrationality measure mu (also called the
> irrationality exponent) as the smallest number mu such that
> |x - p/q| > 1/q^(mu+epsilon)
> holds for any epsilon > 0 and all integers p and q with sufficiently large q.

The symbols in the displayed formula have been transcribed into ASCII; the
retained PDF is authoritative. `pdftotext` produced ordinary text, so no OCR
was used.

PDF page 14 (journal page 418), paragraph headed "World record," lines 676-690
in the same extraction:

> This implies (see, e.g., [Salikhov 2010, Lemma 1]) that the irrationality measure of pi
> is bounded above by ... = 7.10320533413700172750577342281... .

This displayed upper bound is strictly below 8. Therefore the publication
supports the external mathematical input "the irrationality measure of pi is
below 8." The publication and that implication are literature evidence, not a
kernel-checked theorem.

## Normalized source statement

For a real `x`, the source's definition says that an exponent `mu` is an
irrationality-measure upper bound when, for every real `epsilon > 0`, there is
a denominator onset `Q0` such that every integer `p` and every positive integer
`q >= Q0` satisfy

```text
1 / q^(mu + epsilon) < |x - p/q|.
```

The Lean predicate `IrrationalityMeasureBelow x bound` records the existence of
such a `mu < bound`. The cited result supports
`IrrationalityMeasureBelow Real.pi 8`, but the Lean file deliberately receives
that proposition as `hSource`; it does not declare it as a theorem or axiom.

## Quantifier and endpoint audit

- `p` ranges over all integers.
- `q` ranges over positive natural-number denominators.
- The onset may depend on `epsilon`, as "sufficiently large q" permits.
- The source's inequality is strict and has coefficient exactly 1.
- The Lean specialization takes `epsilon = 8 - mu > 0`, so the exponent is
  exactly 8 and gives T2's `EffectiveIrrationality Real.pi 8 1 Q0`.
- T2's pure-resonance conclusion still assumes literal failure of C1. No
  conclusion-equivalent residual-decay or resonance hypothesis is introduced.

## Local verification

From a directory containing these artifacts:

```text
sha256sum zeilberger-zudilin-moscow-2020-9-407.pdf
pdfinfo zeilberger-zudilin-moscow-2020-9-407.pdf
pdftotext -layout zeilberger-zudilin-moscow-2020-9-407.pdf source.txt
```

Search `source.txt` for `we define`, `smallest number`, and `World record` to
inspect the two locators above.
