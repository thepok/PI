# Track F phase 2 report

Date: 2026-09-03 UTC.

Phase 2 was performed in the isolated no-remote clone on branch
`trackF-phase2`, after the requested fast-forward updates from PI main. Nothing
was pushed.

## F4: records and generated views

- Added one quoted record under `knowledge/pi/entries/` for every indexed
  result, open problem, and closed route. F4 bootstrapped the 96 phase-1
  entries; the F6 label audit split two mixed records, leaving 98 records:
  69 results, 12 open problems, and 17 closed routes.
- Each live record has exactly its category schema in YAML front matter and at
  most 20 lines of contiguous, verbatim source quotation. The generator and
  consistency checker enforce the filename, schema, line, and quote rules.
- Added `workflows/verification/build_knowledge.py`. Normal mode regenerates
  the three entry lists in `INDEX.yaml`, the machine-checked status table in
  `FRONTIER.md`, and summary tables atop `ATTEMPT_LEDGER.md` and
  `OPEN_PROBLEMS.md`. `--bootstrap` performs the one-time index-to-record
  conversion; `--check` is read-only and fails on stale views.
- The former ledger and open-problem prose remains byte-for-byte below
  `<!-- generated above; hand-written history below -->`. Repeated builds and
  `--check` established idempotence. `INDEX.yaml` records
  `_meta.generated_by: workflows/verification/build_knowledge.py`.

## F5: one fact, one place

- Replaced the live `knowledge/pi/workstreams/TARGET.md` duplicate with a
  pointer to the frozen specification and moved its complete prior contents,
  verbatim, to
  `knowledge/pi/archive/TARGET_2026-09-03_pre-condensation.md`.
- Replaced the live property-admission audit with a pointer to the compact
  index/records and Document B §6.5. Its complete prior contents are at
  `knowledge/pi/archive/PI_PROPERTY_ADMISSION_AUDIT_2026-09-03_pre-condensation.md`.
- Replaced the live separator roll-up with a pointer to the `SEP-*` records and
  Document A. Its complete prior contents are at
  `knowledge/pi/archive/SEPARATORS_2026-09-03_pre-condensation.md`; the seven
  affected separator records now quote their individual delta files.
- Every move above has an `INDEX.yaml` archive pointer. Exact comparisons
  against the pre-move F4 commit passed.
- `TARGET_SPECIFICATION_v1.md` was not edited: it is byte-identical to the
  phase-2 baseline `ec3f5ed` and has SHA-256
  `4e17661beceec2cd1933119d6fd3a98e5e2eead94b7be8c9b471af3b99782953`.

## F6: executable consistency

Added `workflows/verification/check_knowledge.py` and invoked it from
`workflows/verification/check.ps1`. It checks record/index equality and unique
IDs; the seven-label vocabulary; nonempty Lean names on every
`machine-checked` entry; literal Lean-name occurrence in the audit or
`TheoryLib`; nonempty closed-route separators; existence and repository
containment of document, archive, source, and result paths; reachability of
non-archive knowledge files; exact source quotations; the 20-line limit; and
fresh generated views.

The three phase-1 `unlabelled` registry placeholders required a source-level
audit because `unlabelled` is outside the allowed vocabulary. No explicit
source claim label was changed:

- `AFFINE-FIXED-POINT` now quotes the source sentence that labels the
  statements `conjecture`.
- The mixed `SEP-PAIR-R1` and `SEP-XI3` packets were split into their expressly
  labelled `experiment` and `proof sketch` components.
- All three pre-resolution records are preserved verbatim under
  `knowledge/pi/archive/entries/` and registered in the archive index.

The full gate command passed:

```text
pwsh workflows/verification/check.ps1
```

Its final status was: `PASS: kernel build, tracked-Lean scan, knowledge
consistency, and exact-allowlist axiom audit succeeded.`

## F7: entry-path budget

Final `wc -w` counts after generation:

```text
 382 AGENTS.md
 821 FRONTIER.md
2354 knowledge/pi/INDEX.yaml
3557 total
```

The total is below the requested approximately 3,600-word ceiling (about 4,980
tokens under the repository's 1.4 multiplier).

## Usage

```text
python3 workflows/verification/build_knowledge.py
python3 workflows/verification/build_knowledge.py --check
python3 workflows/verification/check_knowledge.py
pwsh workflows/verification/check.ps1
```

Edit a record, run the generator, then run the gate. Do not hand-edit the
generated portions of the index, frontier table, ledger, or open-problem file.

## Remaining judgments and filesystem exception

- The ID `SOH-3/7` cannot be a literal single POSIX filename because `/` is a
  path separator. Its reversible record filename is `SOH-3%2F7.md`; the ID in
  YAML and generated views remains exactly `SOH-3/7`.
- Splitting the three `unlabelled` placeholders is the only phase-2
  classification judgment. The active quotations expose the source labels and
  the old aggregate records remain available for human label audit.
- Document A still has no article artifact in this public clone, so `docA`
  continues to point at the existing `papers/README.md` stub. The admission
  pointer treats Document B §6.5 plus the per-entry records as the compact
  replacement; the full former audit remains archived if that coverage choice
  needs revision.
- A comparison with the literal historical tree at `2178ffd` shows pre-existing
  snapshot-pin metadata/link edits in the frozen specification. Phase 2 kept
  the `ec3f5ed` baseline file byte-for-byte and neither introduced nor reverted
  those edits.
