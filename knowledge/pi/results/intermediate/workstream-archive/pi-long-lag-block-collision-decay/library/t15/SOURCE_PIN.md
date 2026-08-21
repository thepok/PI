# T15 source pin

The canonical source is local and has no external URL. It was formulated by
this theory program on 2026-07-23.

The immutable workspace source
`knowledge/pi/statements/pi-long-lag-block-collision-decay.txt` was verified as:

```text
db1a5656ab93808f9729f08a2e0cae8c7612d5d3225b41ca791f5f381d90a0c3  knowledge/pi/statements/pi-long-lag-block-collision-decay.txt
```

The exact deterministic definitions used in the note are staged in the
knowledge library from the machine-checked T8 module:

```text
f0c71d2ca404c69f11617f4ddf7587fcc814c897954cf70936a55d8d603f9ee9  knowledge_library/t8/T8SpectralLongLagReduction.lean
```

Relevant T8 locations are the definitions `decimalFrequency`,
`orderedLongPairDomain`, `orderedFirst`, `orderedSecond`, and `spectralSum`,
and theorem `mem_orderedLongPairDomain_iff`. The T15 note rederives every
counting, Fourier, variance, and probability identity it uses.

The T14 note has sketch-level status. Its displayed `Tail(t)` is treated only
as the exact statement under attack, not as a proved premise.
