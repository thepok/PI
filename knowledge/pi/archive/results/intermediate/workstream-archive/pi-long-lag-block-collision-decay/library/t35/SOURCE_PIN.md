# T35 source pin

## Canonical statement

- Local source: `CANONICAL_STATEMENT.txt`
- Original external URL: none; this is a locally formulated problem.
- SHA-256:
  `db1a5656ab93808f9729f08a2e0cae8c7612d5d3225b41ca791f5f381d90a0c3`

## External irrationality input

- Authors: Doron Zeilberger and Wadim Zudilin
- Title: *The Irrationality Measure of Pi is at most 7.103205334137...*
- Journal: *Moscow Journal of Combinatorics and Number Theory* 9 (2020),
  407-419
- DOI: <https://doi.org/10.2140/moscow.2020.9.407>
- Publisher PDF:
  <https://msp.org/moscow/2020/9-4/moscow-v9-n4-p06-s.pdf>
- Retained file: `zeilberger-zudilin-moscow-2020-9-407.pdf`
- Retained SHA-256:
  `3b11c4bf3e25927227ac8f7f4e49d7f1d3efeb42beecd7f3b8c64efb162d20b5`
- Originally retrieved by the T4 source audit: 2026-07-24 UTC
- Rechecked for T35: 2026-08-02 UTC

The definition is on PDF page 2 (journal page 407), Introduction, first
paragraph. It quantifies over every positive epsilon, every integer numerator,
and all sufficiently large positive denominators. The displayed upper bound
`7.10320533413700172750577342281...` is on PDF page 13 (journal page 418),
under "World record". In particular it is strictly below `36/5=7.2`, which
supports the source-pinned eventual exponent used in T35:

```text
|pi-p/q|>q^(-36/5).
```

This is literature evidence, not a Lean theorem or a new axiom. T35 remains a
`proof sketch`.

## Replay

Run `./verify_sources.sh` in this artifact directory. It checks retained bytes
only; it does not certify the mathematical argument.
