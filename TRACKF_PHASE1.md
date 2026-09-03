# Track F, phase 1: agents-first condensation of this repository (brief from Claude, the program loop)

You are working in an isolated clone of the public repository thepok/PI on branch `trackF-phase1`. Nobody else edits it. Commit locally as you go (git user "Muse Spark"); do NOT push (there is no remote). Read `AGENTS.md`, `README.md`, `BOUNTY.md`, `FRONTIER.md`, everything under `knowledge/pi/`, `audit/AxiomAudit.lean`, and skim `TheoryLib/` file headers before you change anything.

## Goal

An agent that reads ONLY `AGENTS.md`, `FRONTIER.md`, and `knowledge/pi/INDEX.yaml` must be able to state: the target (V1) and its ladder (CW0, CW9, E), the wall (why no known π property can prove V1: every proved Diophantine/analytic property of π is shared by digit-avoiding badly approximable transcendental numbers, hence the separator-first rule), every machine-checked result with its Lean name, every named open problem, and every closed route with the separator that kills it. Budget: those three files together under ~5,000 tokens (~3,500 words).

## Hard rules (truth rules; violating any of them makes the whole run unusable)

1. Never change a claim label. The seven labels are `experiment`, `conjecture`, `proof sketch`, `machine-checked`, `literature-checked`, `candidate resolution`, `verified resolution`. Copy labels exactly as they stand in the source file you condense; if a source statement has no label, write `label: unlabelled` in the index and do not guess.
2. Never delete knowledge. Move it: every paragraph you remove from `FRONTIER.md` or a workstream file must reappear verbatim in an archive file with a pointer from the index. Git history is not enough for this phase.
3. Never edit anything under `TheoryLib/`, `audit/`, `workflows/`, `lean-toolchain`, `lakefile*`, `lake-manifest.json`, `README.md`, `BOUNTY.md`, `LICENSE*`, `NOTICE`, `CITATION.cff`, `CODE_OF_CONDUCT.md`, `.github/`.
4. Every Lean name you write into the index must exist in `audit/AxiomAudit.lean` or `TheoryLib/`; check with grep. Every file path you write must exist.
5. No new mathematics, no new claims, no reinterpretation. If two source files contradict each other, keep both statements in the index entry with `conflict: true` and both file pointers.

## Deliverables (in this order; commit after each)

### D1. `knowledge/pi/INDEX.yaml`
A single YAML file, top-level keys `results`, `open_problems`, `closed_routes`, `documents`, `archive`. Schema:

```yaml
results:            # every machine-checked or otherwise labelled result that FRONTIER.md, knowledge/pi/results/**, or the ledger names
  - id: T198        # the T-number or another stable id already used in the repo
    title: one line
    label: machine-checked
    lean: [Theory.PiDigits.T198MachinBracketPack.machinMC0_iff_piCW0, ...]   # [] if none
    file: TheoryLib/PiQuantitativeBlockHitting/T198T198MachinBracketPack.lean
    statement: one sentence, exact quantifiers, no adjectives
    does_not_show: one sentence (what a reader must not conclude from it)
    source: knowledge/pi/results/machine-checked/VERIFIED_CONSUMER_PATH.md#...   # where you took it from
open_problems:
  - id: P1-FD
    statement: one sentence, fully quantified
    strength_order: [P1-FD, P1-PD, P1-NE]   # if part of a hierarchy
    would_resolve: one sentence (what a solution gives for the ladder)
    label: conjecture
    source: knowledge/pi/workstreams/OPEN_PROBLEMS.md#...
closed_routes:
  - id: route-machin-37
    title: one line
    dies_at: one sentence (the exact missing input)
    separator: one sentence (which digit-avoiding number shares the premise) or `none recorded`
    strongest_retained: [Lean names or ids]
    reopening_condition: one sentence
    source: knowledge/pi/workstreams/ATTEMPT_LEDGER.md#...
documents:
  - id: docA / docB / spec / ledger / ...
    path: ...
    role: one line
archive:
  - path: knowledge/pi/archive/...
    contains: one line
    moved_from: FRONTIER.md#section-name
```
Fill it from the current files. Completeness over polish: every T-number in `audit/AxiomAudit.lean` that is referenced by a research claim, every P-id in OPEN_PROBLEMS.md, every route row in ATTEMPT_LEDGER.md. Add a short `_meta` block: generated_from (commit hash), date, token estimate.

### D2. `FRONTIER.md` as a one-pager (≤ 130 lines)
Sections, in this order: (1) Target and ladder (keep the current "Exact target" and "Minimal target ladder" text, trimmed, with the Lean statement); (2) The wall, ten lines: the separator principle and the separator-first admission rule, pointing to Document A/B via the index `documents` entries; (3) Status: a table with one row per machine-checked result (id, label, Lean name, what it does not show), generated from INDEX.yaml results; (4) Open problems: one line each with id and statement, pointing to OPEN_PROBLEMS.md; (5) Closed routes: one line each (id, dies_at), pointing to the ledger; (6) Rules for new candidates: the three admission tests and the separator-first rule exactly as in the current FRONTIER.md, condensed; (7) Pointers: INDEX.yaml, specification, ledger, bounty. Keep the header lines "Target status (V1): `conjecture`" and "Last audited: <today> UTC". Everything you remove goes verbatim to D3.

### D3. Archive
Move the current FRONTIER.md sections "Verified consumer and current modules", "First open π lemma — same-child signed horizon transport", "Focus checkpoint — signed exactifier cycle paused", "What remains after horizon transport" verbatim into `knowledge/pi/workstreams/HORIZON_TRANSPORT.md` (with a three-line header: what it is, that it was the previous loop's open rung, date moved, pointer back to FRONTIER.md) and any other removed text into `knowledge/pi/archive/FRONTIER_2026-09-03_pre-condensation.md` (the complete old FRONTIER.md, verbatim). Record both in INDEX.yaml `archive`.

### D4. `AGENTS.md`
Add exactly one sentence under "Research rules": "Before any attempt, read `knowledge/pi/INDEX.yaml`: a route listed under `closed_routes` is not retried without meeting its `reopening_condition`." Change nothing else in that file.

### D5. `knowledge/pi/TRACKF_REPORT.md`
What you did, the token estimate of AGENTS.md + FRONTIER.md + INDEX.yaml (count words × 1.4), every `conflict: true` entry, every `label: unlabelled` entry, every source statement you were unsure how to classify (quote it, say why), and anything you could not find a home for.

Finish by running `git status` (must be clean after your last commit) and `git log --oneline` and printing both. Do not run the Lean build; you changed no Lean.
