# Pi Lab

**Does every finite string of digits appear somewhere in π?**

Nobody knows. It is not even known whether the digit 7 appears infinitely
often. This repository is a research program on exactly that question, with
a Lean 4 verified core and separately labelled literature reviews, proof
sketches, and experiments. It carries a standing prize:

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

Irrationality, transcendence, and finite irrationality-exponent bounds do not
force decimal word occurrence. Even an irrationality exponent of exactly two
is compatible with a decimal expansion using only 0 and 1. The exact BBP
series and Machin identities identify π, but their known uses here do not
supply the prescribed-target estimates needed for V1. See the
[source review and explicit separator](knowledge/pi/workstreams/OPENAI_MATH_RELEVANCE_2026-10-16.md)
for the distinction and the new exponent-two claim in `openai/math`.

Every proposed route must identify information that distinguishes π from a
suitable word-avoiding replacement and yields a prescribed target hit. The
program makes that requirement explicit and studies both the remaining
π-specific estimates and the intersection problems behind its separators.

## What is inside

| Where | What |
| --- | --- |
| [`FRONTIER.md`](FRONTIER.md) | The research map: target ladder, the first open lemma, admission tests for new ideas. |
| [`openai/math` source review](knowledge/pi/workstreams/OPENAI_MATH_RELEVANCE_2026-10-16.md) | Pinned external results, exact conditional adapters, reusable Lean lemmas, and verification limits. |
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
