# GPT Pro operating guide

This is the persistent guide for the main operator's authenticated web-Pro
research calls. The goal is genuine progress on V1, not a high volume of
memos, reformulations, infrastructure, or formally correct but irrelevant
lemmas.

## Roles and resources

- The main operator owns direction, monitoring, audit, integration, and the
  continuity of the research frontier.
- Keep up to three web-Pro calls active in parallel when useful. Pro is for
  hard creative mathematics only: it does not perform Lean work, routine
  verification, repository editing, workflow design, literature triage, or
  knowledge integration.
- Local subagents independently audit every completed Pro memo. They perform
  any justified Lean formalization and knowledge integration after the result
  survives audit.
- Ox/OpenRouter/OpenCode free-model research remains stopped until Marcel
  explicitly re-enables it.

## Conversation lifecycle

- Never cancel an active Pro call. Pro can be slow; wait patiently and monitor
  its recorded state.
- A Pro conversation may receive **at most five follow-ups**. Once that limit
  is reached, let the active turn finish and start a fresh conversation with a
  compact current-frontier packet. Do not keep extending old conversations.
- If a submitted call is interrupted, resume the identical saved command; do
  not create a duplicate turn. Use a new turn only after proving that the old
  prompt was never submitted.
- If login, account resumption, browser permission, or capacity requires
  Marcel, notify him immediately. Otherwise notify him only for independently
  confirmed substantial mathematical progress.
- Work from GitHub `main` and local `main`. Do not create side branches or ask
  Pro to edit the repository.

## Prompt contract

The persistent operator's full current contract is
[`workflows/research/pi/SIGNED_BRIDGE_OPERATOR_PROMPT.md`](workflows/research/pi/SIGNED_BRIDGE_OPERATOR_PROMPT.md).
Keep that file and this shorter Pro-facing guide aligned.

Keep prompts open but progress-gated. Give Pro a small current packet: the
exact V1 target, the live pi-arithmetic boundary, a few direct links or file
paths, and only the relevant entries from
[`GPTPro/ATTEMPT_LEDGER.md`](GPTPro/ATTEMPT_LEDGER.md). Do not make it map the
repository, and do not constrain it to one operator-invented method.

State the central bottleneck plainly: the repository already has abundant
exact BBP, Machin, p-adic, denominator, fibre, irrationality, generic-dynamical,
and rational-shadow structure, but those routes repeatedly lose the
Archimedean, target-dependent sign needed by the consumer. More local structure
is unlikely to bridge that gap by itself. The current program is therefore to
build a small pi-specific signed bridge theory, not to derive V1 once more from
the existing representation library.

Its provisional summit is

```text
forall k >= 3, forall A < 10^k, exists N >= 10^k:
  Re (primitiveBoundaryFourierSum (10^k) A N) >= 0.
```

Permit an explicitly stronger or shorter-to-V1 theorem. Work backward, and
require every proposed component to answer: **where does the target-signed
Archimedean information for the actual constant pi enter?** Symmetry, mean
zero, almost-everywhere behavior, denominator size, periodicity, local
congruences, unsigned energy, and rational shadows are not sources of that
information by themselves.

Ask for a genuinely new positive theorem, quantitative estimate, or exact
pi-specific mechanism with explicit quantifiers and a concrete implication to
a verified V1 consumer. A decisive no-go is useful only when it closes a live
route rather than polishing an already archived obstruction. Equivalent
criteria, denominator-only facts, fixed-modulus projections, unsigned
averages, kernel changes, generic countermodels, and representation-only
identities are not frontier progress by themselves.

The current mode is a single constructive signed-horizon-transport program,
not an open-ended empirical phenomenon search. T189 is fixed as the completed
consumer. Differentiate the three slots around one shared lemma ladder:

On the natural-diagonal FMR frontier, the literal `Xi_d` threshold is only an
equivalent coordinate form of FMR. The first honest backward split preserves
the witness:

```text
S_+={d<10:D_d>0};
(R1) S_+ is nonempty;
(R2) exists d in S_+: G_d+D_d>0.
```

R1 is the first strictly weaker pi-specific rung; R2 is the same-digit
alignment/deficit-cover rung. Never replace them with separate existential
witnesses or silently universalize an existential reached path.

1. design the backward ladder from the positive pi seed to new target-signed
   mass at a growing horizon;
2. try to prove the first genuinely pi-specific unproved rung;
3. attack exactly that rung adversarially, proving its critical step or
   closing it with a narrow separator.

The operator decomposes a failed rung and reassigns the smaller atomic step;
it does not restart a broad search after every failure. Empirical work is used
only to falsify a concrete proposed rung quickly. CM, BBP, Machin, modular,
Padé, hypergeometric, or other representations are admissible only when they
feed that named rung rather than merely recoding the carrier.

Use PaperSearch early as mathematical building material and do a serious
literature comparison before treating an idea as new. Do not let known theory
confine the search to standard routes. Separate almost-everywhere theorems for
lacunary sequences from results applicable to the explicit constant pi, and
record exactly which hypothesis fails. Put at most three relevant
attempt-ledger warnings in one prompt; the ledger is memory, not a
creativity-limiting catalogue.

Use a follow-up only when an audited memo has genuine momentum: a new
supportable statement with one sharply identified remaining step. A no-go,
representation identity, or broad failed search ends the conversation even if
fewer than five follow-ups were used. Five is a ceiling, not a target.

## Required answer shape

The main body is a self-contained mathematical memo: exact statement,
derivation, stress test, claim boundary, and shortest verified consumer path.
End it with a compact **attempt ledger** listing every substantive route tried
during that turn:

1. route or mechanism;
2. strongest proposed lemma;
3. first fatal line, or the exact surviving open step;
4. genuinely new input required to reopen or finish it.

The list prevents later Pro calls from unknowingly repeating discarded work.
The operator audits and deduplicates it into `GPTPro/ATTEMPT_LEDGER.md`; only
the few relevant entries go into any one future prompt.

## Trust and integration

- Pro output is untrusted, even when confident or detailed.
- Independently check constants, quantifiers, theorem semantics, novelty, and
  the claimed consumer before editing canonical knowledge.
- Integrate only correct and materially new results, with the repository claim
  vocabulary and precise limitations. Preserve useful negative results, but
  do not bloat the knowledge base with duplicate failure analyses.
- Do not formalize another representation theorem unless a specific current
  proof attempt shows how it feeds a required sign, correlation, entropy, or
  other named consumer bound.
- Lean changes must pass the strict verifier and axiom audit. A green build
  means machine-checked, not that V1 or novelty has been established.
- Keep `FRONTIER.md` concise and current. Prefer mathematical progress over
  scaffolding, navigation systems, or workflow refinement.
