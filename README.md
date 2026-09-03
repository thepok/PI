# Pi Lab

**Does every finite string of digits appear somewhere in π?**

Nobody knows. It is not even known whether the digit 7 appears infinitely
often. This repository is a research program on exactly that question, with
every result machine-checked in Lean 4, and it carries a standing prize:

> ## 💰 USD 10,000 for a Lean proof
>
> Paid to the first person who submits a pull request proving
> `Theory.PiDigits.V1`, exactly as stated in
> [`TheoryLib/PiDigits/T7Statements.lean`](TheoryLib/PiDigits/T7Statements.lean),
> that builds with the pinned toolchain and uses no axioms beyond
> `propext`, `Classical.choice`, and `Quot.sound`.
> Full rules: [`BOUNTY.md`](BOUNTY.md).

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

Every property of π that has ever been proved (irrationality, transcendence,
the irrationality-exponent bound 7.1032…, the BBP digit-extraction formula,
Machin-type identities) is also satisfied by numbers whose decimal expansion
*avoids* a chosen digit string entirely. Such numbers exist in abundance:
badly approximable, transcendental, and living inside every deleted-digit
Cantor set. Any proof of V1 therefore needs an input that those numbers do not
have, and no such input is known. The program here makes that wall explicit,
theorem by theorem, and reduces the problem to a single named question about
the intersection of two well-studied sets of real numbers.

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

## Papers

Two companion manuscripts (a research article on the separator theorems and
the open intersection problem, and a technical note with the exact
reformulations and route audits) are in preparation. Citation details will be
added here when they are posted.
