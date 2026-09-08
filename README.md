# Pi Lab

**Does every finite string of digits appear somewhere in π?**

Nobody knows. It is not even known whether the digit 7 appears infinitely
often. This repository is a research program on exactly that question, with
a Lean 4 machine-checked core, separately labelled proof sketches and
experiments, and a standing prize:

> ## 💰 USD 10,000 for a Lean proof
>
> Paid to the first person who submits a pull request proving
> `Theory.PiDigits.V1`, exactly as stated in
> [`TheoryLib/PiDigits/T7Statements.lean`](TheoryLib/PiDigits/T7Statements.lean),
> that builds with the pinned toolchain and uses no axioms beyond
> `propext`, `Classical.choice`, and `Quot.sound`.
> Offered by Marcel Richter, who already spends a few hundred dollars a month
> on this question and considers that a bargain. Full rules:
> [`BOUNTY.md`](BOUNTY.md).

```lean
/-- V1 (canonical): every finite decimal digit string occurs contiguously in pi. -/
def V1 : Prop :=
  ∀ s : List (Fin 10), ∃ n : ℕ, ∀ i : ℕ, ∀ hi : i < s.length,
    piDigit (n + i) = s.get ⟨i, hi⟩
```

Nothing in this repository proves V1. What it contains is the map of where
the known roads end, and a precise statement of the first thing anyone would
have to prove to get past them.

## Why this is hard

Several coarse properties of π—irrationality, transcendence, and finite
irrationality-exponent upper bounds—are compatible with avoiding a prescribed
decimal word. The [separator theorem](knowledge/pi/results/intermediate/20260902-diophantine-separator-theorems.md)
(`proof sketch`) gives badly approximable transcendental word-avoiders with
irrationality exponent 2; it states the precise scope of this comparison.

This does **not** mean another number satisfies π's fixed BBP series or fixed
Machin identity: those uniquely specify their value. The missing step is to
deduce unbounded decimal word occurrences from the actual coefficients and
canonical data of π, not merely from a representation's existence or coarse
approximation bounds. The [research map](FRONTIER.md) records the open target
ladder and the inputs still missing from the investigated routes. These scoped
limitations are not a theorem that every arithmetic approach must fail.

## What is inside

| Where | What |
| --- | --- |
| [`FRONTIER.md`](FRONTIER.md) | The research map: target ladder, the first open lemma, admission tests for new ideas. |
| [`TheoryLib/`](TheoryLib/) + [`audit/AxiomAudit.lean`](audit/AxiomAudit.lean) | The verified Lean core. Every theorem behind a research claim is registered in the audit. |
| [`knowledge/pi/workstreams/`](knowledge/pi/workstreams/) | Target specification, named open problems, the attempt ledger (what was tried, why it died, what would reopen it). |
| [`knowledge/pi/results/`](knowledge/pi/results/) | Machine-checked, intermediate, and negative results. |
| [`workflows/`](workflows/) | Reproducible experiments and the verification gate. |

Verify the Lean core and the axiom audit with:

```powershell
pwsh workflows/verification/check.ps1
```

## Rules of the house

- No `sorry`, `admit`, `native_decide`, or new axioms. Ever.
- Finite computation falsifies and refines; it never proves.
- Claims use exactly one label: `experiment`, `conjecture`, `proof sketch`,
  `machine-checked`, `literature-checked`, `candidate resolution`,
  `verified resolution`. Labels are never upgraded silently.
- Before building on a property of π, run the separator test: if a
  digit-avoiding number shares the property, it cannot prove V1.

## Contributing

Pull requests are welcome for verified Lean results, falsification
experiments, and corrections to the ledger. A named, testable, surprising
conjecture about π, with an experiment that could kill it, is worth more here
than another closed route. Read [`AGENTS.md`](AGENTS.md) first; it applies to
humans and agents alike.

## License and citation

Lean sources, scripts, and build configuration are under the
[Apache License 2.0](LICENSE). `FRONTIER.md`, everything under `knowledge/`,
and the target specification are under [CC BY 4.0](LICENSE-docs). The π-digit
data file carries its own provenance note in
[`workflows/experiments/data/README.md`](workflows/experiments/data/README.md).
Contributions are accepted under the license of the path they touch.

Cite the repository with GitHub's **Cite this repository** button, generated
from [`CITATION.cff`](CITATION.cff); a Zenodo DOI is added there at the first
release.

## Papers

Drafts and citation guidance for the research article and technical companion
note are available under [`papers/`](papers/).
