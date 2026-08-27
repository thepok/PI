# T14 source pin

The canonical statement is the immutable workspace source
`knowledge/pi/statements/pi-long-lag-block-collision-decay.txt`. Its verified hash is:

```text
db1a5656ab93808f9729f08a2e0cae8c7612d5d3225b41ca791f5f381d90a0c3  knowledge/pi/statements/pi-long-lag-block-collision-decay.txt
```

The exact deterministic definitions used by the note come from the
machine-checked knowledge-library module
`TheoryLib.PiLongLagBlockCollisionDecay.T8T8SpectralLongLagReduction`.

```text
f0c71d2ca404c69f11617f4ddf7587fcc814c897954cf70936a55d8d603f9ee9  T8SpectralLongLagReduction.lean
```

Relevant source locations in that module are:

- lines 37-42: `decimalFrequency m = 10^m`;
- lines 44-68: oriented pair coordinates and `orderedLongPairDomain`;
- lines 70-94: exact domain membership equivalence;
- lines 96-123: phase and positive-frequency spectral sum; and
- lines 154-159: inclusive frequency range `1 <= h <= 10^m`.

The arithmetic predicate expanded in the note is defined in
`Theory.PiDigits.PositiveLowerBlockDensity.T25` by
`structuredDenominator n r = 10^n * (10^r - 1)` and

```text
86639d8f8adbb5cf54a474fe89760cbeecd243e9f0bcb3768a16a23dab3ee88c  T25_ARITHMETIC_EXCLUSION_SOURCE.txt
```

```text
ArithmeticExcluded mu c Q0 m n r :=
  Q0 <= structuredDenominator n r and
  (10^m)^(-1) <= structuredDenominator n r *
    (c / structuredDenominator n r ^ mu).
```

No external literature theorem is invoked. The T10 and T11 prose notes are
sketch-level context only and supply no premise to the T14 derivations.
