# Pi Lab

This repository studies the open question whether every finite decimal word
occurs in the decimal expansion of π. Nothing here proves that statement.

Start with [`FRONTIER.md`](FRONTIER.md). It is the current mathematical map;
the proof authority is [`TheoryLib/`](TheoryLib/) together with
[`audit/AxiomAudit.lean`](audit/AxiomAudit.lean).

## Active surface

- [`FRONTIER.md`](FRONTIER.md): exact live frontier and first open π-specific rung.
- [`knowledge/pi/active/`](knowledge/pi/active/): the small active knowledge core.
- [`knowledge/pi/active/ATTEMPT_LEDGER.md`](knowledge/pi/active/ATTEMPT_LEDGER.md): compressed memory of attempted route families.
- [`knowledge/pi/active/SEPARATORS.md`](knowledge/pi/active/SEPARATORS.md): at most ten currently relevant no-go results.
- [`TheoryLib/`](TheoryLib/): canonical Lean source.
- [`audit/AxiomAudit.lean`](audit/AxiomAudit.lean): explicit theorem axiom audit.
- [`workflows/`](workflows/): experiments, Pro runtime state, and verification.
- [`knowledge/pi/archive/`](knowledge/pi/archive/): historical material, excluded from normal navigation and prompts.

The sole research branch is `main`. Pro models read `main` and return
self-contained mathematical memos; they do not edit the repository.

## Current program

The fixed consumer is T189's fresh-monotone regeneration frontier. At a
positive natural-diagonal node, define old child gain `G_d` and fresh gain
`D_d`. The exact remaining condition is

```text
exists d < 10: D_d > 0 and G_d + D_d > 0.
```

The first honest split keeps the same witness:

```text
R1: S_+ = {d : D_d > 0} is nonempty.
R2: exists d in S_+ with G_d + D_d > 0.
```

The missing mathematics is a π-specific source of target-signed
Archimedean information that proves R1 and then aligns the same digit for R2
on an unbounded, consistently reached path. Symmetry, mean zero,
almost-everywhere lacunary theorems, denominator growth, congruences, unsigned
energy, rational shadows, and finite π-prefix evidence do not supply it.

## Admission and trust

A result counts as frontier progress only if it proves a new actual-π signed
estimate, closes a named live premise, strictly improves the consumer with a
checked implication, or narrowly retires a live route. Equivalent criteria,
new representations, more finite replay, and workflow changes are not
mathematical progress.

Use only these claim labels: `experiment`, `conjecture`, `proof sketch`,
`machine-checked`, `literature-checked`, `candidate resolution`, and
`verified resolution`.

Formal work may not use `sorry`, `admit`, `native_decide`, new axioms, unsafe
declarations, or compiler-trusting shortcuts. Every research theorem belongs
in the axiom audit. Run:

```powershell
pwsh workflows/verification/check.ps1
```

A green build means machine-checked only. It does not mean novel, relevant,
or a solution of V1.

## Clean-knowledge rule

The active knowledge surface is intentionally capped at 20–40 files. Every
active file must serve the exact target, shortest consumer path, T189/FMR,
the first open π lemma, one of at most ten live separators, or the compressed
attempt ledger. Superseded material moves to the archive; it is never copied
back into prompts merely because it exists. Keep navigation short, links
current, and one fact in one canonical active place.
