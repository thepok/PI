# T47 source pin

## Canonical statement

- Local source: `CANONICAL_STATEMENT.txt`
- Original external URL: none; this is a locally formulated problem.
- SHA-256:
  `db1a5656ab93808f9729f08a2e0cae8c7612d5d3225b41ca791f5f381d90a0c3`

## External irrationality input used in T47

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
- Rechecked byte-for-byte for T47: 2026-08-02 UTC

The definition is on physical PDF page 2 (journal page 407), Introduction,
first paragraph. It defines the irrationality measure as the smallest `mu`
such that, for every positive `epsilon` and all integers `p,q` with
sufficiently large positive `q`,

```text
|x-p/q| > q^(-(mu+epsilon)).
```

The displayed conclusion under "World record" on physical PDF page 13
(journal page 418) is that the irrationality measure of `pi` is bounded above
by

```text
7.10320533413700172750577342281... .
```

This number is strictly below `36/5 = 7.2`. Choosing the positive gap to
`36/5` as epsilon in the source definition gives an onset `Qstar` such that,
for every positive integer `d >= Qstar` and every integer `p`,

```text
|pi-p/d| > d^(-36/5).
```

Taking `p` to be a nearest integer to `d*pi` and multiplying by `d>0` gives
the exact consequence used in Section 8 of the T47 note:

```text
||d*pi|| > d^(-31/5),
```

where `||x||` is distance to the nearest integer. This is literature evidence,
not a Lean theorem or a new axiom. T47 remains a `proof sketch`; its scaling
obstruction is conditional on the cited publication's irrationality-measure
claim.

## Replay

Run `./verify_sources.sh` in this artifact directory. It checks the retained
canonical statement and publisher PDF bytes only; it does not certify the
mathematical argument.
