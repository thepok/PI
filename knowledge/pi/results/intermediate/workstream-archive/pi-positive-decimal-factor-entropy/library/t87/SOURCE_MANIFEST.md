# T87 source manifest

Accessed and checked: 2026-08-03 UTC.

## Canonical statement

- File: `pi-positive-decimal-factor-entropy.txt`
- SHA-256: `a70dd741b27595aeb3dfc902b5e201579fed6bae24e2191f58c5ac64a22939e6`
- Provenance: locally formulated; there is no original external URL.
- Use: exact canonical question and recorded sibling variants.

## Primary source

- ID: ZZ20
- Authors: D. Zeilberger and W. Zudilin
- Title: *The irrationality measure of pi is at most 7.103205334137...*
- Journal: Moscow Journal of Combinatorics and Number Theory 9 (2020),
  407--419
- DOI: <https://doi.org/10.2140/moscow.2020.9.407>
- PDF file: `zeilberger-zudilin-2020.pdf`
- PDF SHA-256: `3b11c4bf3e25927227ac8f7f4e49d7f1d3efeb42beecd7f3b8c64efb162d20b5`
- Text extraction: `zeilberger-zudilin-2020.txt`
- Text SHA-256: `49ca4907538e4ccea23cee27f051f5b33832ed2cf3e3093b4aab58a13c814a68`
- Locators: definition and quantifiers, printed p. 407; Propositions 7--8
  and equation (18), printed pp. 417--418; final exponent
  `7.10320533413700172750577342281...`, printed p. 418.
- Checked use: choosing the rational exponent `7.104=888/125` strictly
  above the published bound yields one eventual denominator onset `Q0` and
  the lower bound used in T87. The paper does not print a numerical `Q0`.

The text file was produced by `pdftotext -layout`. It is a locator aid; the
PDF is authoritative.

## Kernel-checked imports

These accepted library modules are not duplicated in the delivery.

| Module | SHA-256 | Use |
|---|---|---|
| `TheoryLib.PiPositiveDecimalFactorEntropy.T61T61VaalerAnalytic` | `61bf75193b6581ef626fc2b061ea6ba39e4fc164ac9e49b3a0820528dc839993` | Exact T61 ranges, weights, endpoints, majorant, and conditional chain. |
| `TheoryLib.PiPositiveDecimalFactorEntropy.T86T86GroupedSquareBound` | `29106f3d3d96a0342a50571d3cd62f1d64d4dbd13b5c9c11f514e5993d45f87b` | Exact grouping, fibers, one-scale envelope, and cumulative `<42` bound. |

## Roadmaps not used as premises

The T60 and T83 notes are `proof sketch` artifacts. They suggested formulas
to audit, but no claim from either note is treated as established. T87
rederives its cutoff, counts, exponent loss, and covariance frontier from the
kernel-checked interfaces and the pinned primary source above.
