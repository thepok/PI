# Salikhov to the T17 power-of-ten premise

Status: Salikhov source statement `literature-checked`; source-to-T17
derivation `proof sketch`. C1 remains a `conjecture`.

## Supported conclusion

The recorded Salikhov bound supports the external statement

```text
∃ A : ℕ, 1 ≤ A ∧ PowerTenDiophantine Real.pi 8 A.
```

For the exponent `ν = 8`, let `Q₀` be the source's denominator onset and
choose any `A ≥ 1` with `Q₀ ≤ 10^A`. If `A ≤ t`, then `q = 10^t` clears the
source threshold and

```text
1 / 10^(8*t) ≤ |pi - p / 10^t|.
```

Positive integer `p` is covered directly by Salikhov. For `p ≤ 0`, the bound
is elementary because the approximation lies at or below zero. The restriction
`1 ≤ A` is real: `A = 0` fails at `t = 0`, `p = 3` since `|pi - 3| < 1`.

Here `8` is the smallest natural exponent obtained directly from the recorded
bound `7.60630852...`; no rounded endpoint is asserted. The source statement
does not expose a numerical `Q₀`, so it does not justify a numerical `A`.

## Existing formal overlap and boundary

This does not add a missing Lean bridge. Canonical T35 already
machine-checks

```text
IrrationalityMeasureBelow Real.pi 8 →
  ∃ A, PowerTenDiophantine Real.pi 8 A.
```

GP-0001 is useful as a direct Salikhov-specific source and edge-case audit,
but adds no formal capability. Kernel-internally, the literature theorem
remains an explicit hypothesis; no source theorem was added as an axiom.
Externally, the power-of-ten premise is supported, but this supplies no
Fourier cancellation, signed cell-occupancy bound, density, prescribed word,
or V1 conclusion. The live bottleneck remains a numerator-sensitive estimate
for the exact synchronized BBP residues.

## Source and verification

- V. Kh. Salikhov, *On the irrationality measure of pi*, Russian Mathematical
  Surveys 63 (2008), 570–572, DOI `10.1070/RM2008v063n03ABEH004543`.
- retained PDF SHA-256:
  `a871a3fd09a7d606c3b0d6402094e2af7777bf007254aec89a36aee2150ab60d`.
- independently regenerated `pdftotext -layout` SHA-256:
  `e05fcf2c6941386ab51d0bb2705110f4e67660d7669d9f2a92d9c3e9a9466699`.
- T17 source SHA-256:
  `165dcd2b5f6339a9aa42285aff617c11c89c140a04fba26e0fcde3c3828338c1`.
- GPTPro provenance commits: `073165ee4c24292cd98999b0f6ae8f831d70a9f2`
  and `4babe6b4861b224c609979a633d8c9fc7569bba9`.

The flattened historical T9 replay bundle is not currently replay-clean:
`reproduce.sh` retains obsolete paths, its root calculation is stale, and two
manifest-side hashes no longer match the flattened Markdown/JSON files. The
retained primary PDF itself matches its recorded hash, and independent text
regeneration matches the recorded extraction hash. This report therefore does
not claim that the entire archival replay passes.
