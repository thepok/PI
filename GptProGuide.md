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

Keep prompts open but progress-gated. Give Pro a small current packet: the
exact V1 target, the live pi-arithmetic boundary, a few direct links or file
paths, and only the relevant entries from
[`GPTPro/ATTEMPT_LEDGER.md`](GPTPro/ATTEMPT_LEDGER.md). Do not make it map the
repository, and do not constrain it to one operator-invented method.

Ask for a genuinely new positive theorem, quantitative estimate, or exact
pi-specific mechanism with explicit quantifiers and a concrete implication to
a verified V1 consumer. A decisive no-go is useful only when it closes a live
route rather than polishing an already archived obstruction. Equivalent
criteria, denominator-only facts, fixed-modulus projections, unsigned
averages, kernel changes, generic countermodels, and representation-only
identities are not frontier progress by themselves.

Differentiate the three slots by default—decimal-orbit exponential sums, exact
BBP arithmetic, and a free alternative pi-specific route—but let each model
abandon its starting direction when another idea is mathematically stronger.
When an audited memo has a substantive surviving step, use a follow-up to
attack that step. Otherwise start the next fresh investigation without asking
for more polish of the failed route.

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
- Lean changes must pass the strict verifier and axiom audit. A green build
  means machine-checked, not that V1 or novelty has been established.
- Keep `FRONTIER.md` concise and current. Prefer mathematical progress over
  scaffolding, navigation systems, or workflow refinement.
