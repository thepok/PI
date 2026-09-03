# Track F phase 1 report

Date: 2026-09-03 UTC.

## Work completed

- Baseline update: `git -C /home/Marcel/dev/PI pull --ff-only` reported current. The clone's required fast-forward pull stopped because its local setup commit `686b809` diverged from current main `7561ece`; after confirming the topology and clean tree, that setup commit was rebased onto main as `21efcd6`. No research content was selected between conflicting versions.
- D1: created `knowledge/pi/INDEX.yaml` with 67 results (47 referenced T-results plus 20 non-T result records: 17 explicitly labelled and three aggregate unlabelled records), all 12 formula-tagged open problems, all 17 ledger routes, eight document pointers, two archive pointers, and metadata. All 48 listed Lean declarations were found in `audit/AxiomAudit.lean` or `TheoryLib/`; every listed path exists.
- D2: replaced `FRONTIER.md` with a 127-line one-pager. Its 47-row machine-checked table and its open/closed lists were generated from the index.
- D3: preserved the complete former 491-line `FRONTIER.md` byte-for-byte in `knowledge/pi/archive/FRONTIER_2026-09-03_pre-condensation.md`; preserved the four requested sections byte-for-byte after the three-line header in `knowledge/pi/workstreams/HORIZON_TRANSPORT.md`.
- D4: added exactly the requested one sentence under `AGENTS.md` Research rules.
- Verification: YAML parsing, ID/count equality, allowed-label checks, path checks, Lean-name grep checks, frontier/index table equality, line limit, archive byte comparisons, and `git diff --check` passed. Per the brief, no Lean build ran. Nothing was pushed.

## Agent-entry token estimate

`wc -w` gives `AGENTS.md=382`, `FRONTIER.md=909`, and `knowledge/pi/INDEX.yaml=2085`: total `3376` words. The requested estimate is `3376 × 1.4 = 4726.4`, rounded to `4726` tokens.

Final index counts: `results=67`, `open_problems=12`, `closed_routes=17`.

## Conflicts

Index entries with `conflict: true`: none; no contradictory research statements requiring dual preservation were found.

One operational instruction differed: the committed brief says git user “Muse Spark,” while Marcel's direct task says “Codex” / “codex@pilab.local.” The direct task was followed; this is not a research-index conflict.

## Unlabelled entries

Index entries with `label: unlabelled`: `AFFINE-FIXED-POINT`, `SEP-PAIR-R1`, and `SEP-XI3`.

## Classification uncertainties retained at source

No indexed mathematical claim was given a guessed label. These source packets mix explicitly different labels; the index isolates a same-label component where possible and uses `unlabelled` for the three aggregate source statements that have no single explicit label:

- `20260828-central-carrier-annular-flux.md`: “Claim label: universal identities and inequalities are `proof sketch` (independently audited); the fixed hard-node values are an `experiment`.” One aggregate label would erase that division.
- `20260828-sector5-odd-frequency-machin-direction.md`: “the T169/T179/T189 inputs are `machine-checked`,” the reductions are “`proof sketch`,” and the node computation is an “`experiment`.” These are three claim classes.
- `20260902-pro-conjecture-mining-cycle1.md`: “Status: `experiment` (reconnaissance reproduced), statements are `conjecture`.” The evidence and proposed laws have different labels.
- `20260827-pair-r1-laurent-transcendence-boundary.md`: “the elementary DFT/transcendence deductions are `proof sketch`” and “the actual-pi node separator below is an `experiment`.” The file has no single aggregate label.
- `20260827-xi3-all-three-fixed-point-separator.md`: “the T179/T189 identities are `machine-checked`; the directed numerical enclosure is an `experiment`; the finite-prefix and transcendental continuation arguments are `proof sketch`.” The components remain separately labelled at source.

Their machine-checked T-results and labelled non-Lean records are indexed, their route implications are represented in `closed_routes`, and the source files remain unchanged.

## Items without a public artifact home

- Document A, “Decimal word avoidance, badly approximable separators, and the BA–ALA intersection problem,” is described in `papers/README.md` as “research article to be added later.” Because no article file exists in this clone, index entry `docA` points to that existing bibliographic stub rather than inventing a path.
- The mining-cycle note says its other three conjectures “are recorded in the project repository only.” That private repository is outside this public clone, so no public path could be indexed; the two retained public statements remain in their existing note.

Everything present in this clone and required by the phase-1 brief has an indexed or archived home.
