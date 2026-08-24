# Pi Lab

A compact, machine-checked research workspace for the question:

> Does every finite digit string occur in the decimal expansion of π?

No theorem in this repository resolves that question. A green build means only
that the stated Lean declarations are machine-checked under the exact axiom
allowlist. It does not establish novelty, statistical randomness, normality,
density, or decimal disjunctivity.

Read [`FRONTIER.md`](FRONTIER.md) before proposing or starting mathematical
work. It gives the concise current implication graph, the strongest verified
fixed-π results, and the quantitative estimate that is still missing. It is an
orientation document; the proof authority remains `TheoryLib/` together with
the explicit axiom audit.

## Repository map

- `TheoryLib/` and `TheoryLib.lean`: canonical Lean proof source.
- `audit/AxiomAudit.lean`: explicit theorem-by-theorem axiom audit.
- `FRONTIER.md`: concise statement of the live mathematical frontier.
- `knowledge/pi/`: statements, milestone reports, negative results,
  continuation state, and active workstreams.
- `workflows/`: sandboxed model runners, task definitions, runtime/container
  tools, and verification scripts.
- `GPTPro/`: file-based coordination and concrete deliverables for separately
  invoked high-capability research models.

## Research admission policy

The project does not treat theorem count, task count, model consensus, or
formal representation depth as evidence of progress. Before a task is admitted,
it must identify one exact open edge in [`FRONTIER.md`](FRONTIER.md), name the
quantity to be bounded or the implication to be improved, and state what would
constitute failure.

A new theorem belongs on the main research path only if it does at least one of
the following:

1. proves a new unconditional quantitative estimate for the actual decimal π
   orbit or the exact sampled BBP orbit;
2. strictly weakens an existing sufficient premise, with a checked implication
   to the old endpoint and a concrete separator showing strictness;
3. closes a named external premise used by a live proof chain;
4. gives a decisive counterexample or no-go theorem that retires a live route;
5. repairs a concrete trust-boundary defect in the verification system.

Everything else may still be useful as supporting infrastructure, an
`experiment`, a `proof sketch`, or a negative result, but it must not be
presented as frontier progress.

### Avoid by default

Do not spend research capacity on the following unless the task contract states
a new hypothesis or mechanism that escapes the recorded obstruction.

- **More equivalent formulations of V1.** Orbit density, arbitrarily-late
  density, return statements, symbolic coverage, and BBP-shadow density are
  useful interfaces, but another equivalence does not make either side true.
- **Representation-only theorem chains.** Exact rational normal forms, GCD
  decompositions, carry identities, residue coordinates, CRT packaging,
  p-adic fibres, and successor recurrences are not progress unless they prove a
  nontrivial occupancy, collision, anti-concentration, or cancellation estimate
  for the actual normalized sequence.
- **Repackaged BBP or Machin heuristics.** Complicated forcing is not mixing.
  The sampled BBP orbit is asymptotic to the original decimal π orbit; a BBP
  route must produce a genuinely new fixed-π quantitative estimate.
- **Generic conditional consumers with no new input.** A theorem of the form
  “if the orbit has the required distribution bound, then V1 follows” is useful
  only when it is strictly sharper than the existing consumer or when the
  missing premise is itself being attacked. Do not duplicate the archived
  Fejér, self-return, or long-lag frontier under new notation.
- **Qualitative facts presented as distribution.** Irrationality,
  transcendence, non-eventual periodicity, the bound `p_π(k) ≥ k + 1`, and an
  unbounded additive fixed-frequency Fourier gap do not imply decimal density.
- **Finite digit searches presented as evidence for V1.** Computation may
  locate a particular word, falsify a proposed scaling law, or expose a
  resonance. It cannot prove a statement quantified over all word lengths.
- **Model output presented as evidence.** Worker agreement, referee votes, and
  successful artifact contracts are triage signals only. They are not
  mathematical validation.
- **Workflow expansion without a blocking defect.** Do not add orchestration,
  schemas, prompts, dashboards, providers, or agent roles merely to create more
  activity. Repair workflow code only when a concrete research or verification
  operation is failing.
- **Reopening archived no-go routes unchanged.** A retired direction may be
  reopened only by naming the exact counterexample or obstruction and stating
  the new ingredient that invalidates it.

A new `T` number is not a milestone by itself.

## Active mathematical targets

### 1. Direct Fourier target

Let

```text
S_h(N) = ∑_{n < N} exp(2π i h fract(10^n π)).
```

The machine-checked
[`T123`](TheoryLib/PiQuantitativeBlockHitting/T123T123AggregatedJacksonFrontier.lean)
frontier first groups equal Jackson frequencies. The still sharper
[`T124`](TheoryLib/PiQuantitativeBlockHitting/T124T124DirectionalJacksonFrontier.lean)
consumer retains the signed real sum centered on one target word. It reduces
V1 to the following wordwise sufficient condition: for every
nonempty decimal word `s`, find one `N_s > 0` such that

```text
directionalJacksonDefect(piOrbit, N_s, 10^|s|, cylinderLeft(s))
  < 1 / (3 * 10^|s|) + 2 / (3 * 10^(3*|s|)).
```

The checked hierarchy is

```text
T19 pointwise → raw Jackson load → aggregated load → directional word test → V1.
```

Actual-Jackson finite separators machine-check strictness at the raw-to-
aggregated and aggregated-to-directional steps, including an exact `q=10`
directional separator. They do not prove a logical
separation of the pi-level predicates, and none of those predicates is proved
for pi.

A newer boundary-matched cosine--Fejer minorant matches the exact cylinder
boundary. T128 machine-checks its finite Fourier closed form, outside-sign
property, coefficientwise domination of the old Jackson coefficients, positive
explicit zero-mode lower bound, and finite directional hitting consumer. The
sharper normalized-coefficient comparison and genuine `q=10` separators remain
an independently audited `proof sketch`; its fixed-pi premise remains open.

The current unconditional fixed-frequency results give only additive gaps and
do not approach this moving-frequency normalized estimate. Future Fourier work
must bound the actual directional or aggregated quantity on the growing
natural-scale frequency window, strictly weaken this sufficient premise, or
rigorously prove that a proposed route cannot do so.

### 2. Moving-mesh occupancy-tail target

For a selected block `[L, 2L)` and a partition into `q` equal cells, let `n(a)`
be the number of orbit points in cell `a`. The weakest reviewed Haar consumer
currently asks for uniform integrability of the cell-smoothed densities:

```text
lim_(M→∞) sup_j (1/L_j)
  ∑_{a : n_j(a) > M L_j/q_j} n_j(a) = 0.
```

Together with `L_j,q_j→∞` and vanishing averaged pseudo-orbit error, this tail
condition forces selected-block Haar limits and hence fixed-cylinder hits. The
older collision second-moment bound and the intermediate bounded-entropy-
deficit premise both imply this condition; reviewed exact decimal de Bruijn
stages separate the converses.

The consumers and separators are currently `proof sketch`; more importantly,
the displayed tail estimate is not proved for the decimal π orbit or the
sampled BBP orbit. The valuable work is to prove, sharpen, or falsify that
fixed-π premise, not to restate the consumer.

Effective irrationality alone is now decisively excluded as a route to this
tail premise: an audited sparse-decimal seed has irrationality exponent at
most `3`, satisfies an explicit exponent-`4` effective bound, and nevertheless
fails UI on every moving-mesh selection. T126 machine-checks its local
zero-window-to-first-cell mechanism; the full separator remains `proof sketch`.

### Priority order

1. Prove or falsify a fixed-π Fourier or UI estimate at the required
   moving scale.
2. Find a strictly weaker sufficient condition and certify the strict
   improvement.
3. Formalize an external theorem only when it closes a named premise on a live
   path.
4. Build supporting representation lemmas only when a current proof attempt has
   reached a precise missing identity that blocks one of the items above.
5. Use experiments to kill bad conjectures early, not to accumulate favorable
   statistics.

## Required task contract

Every mathematical task given to a model or human collaborator must state:

- the repository branch and exact source theorem or report;
- the open premise or quantity being attacked;
- the proposed deliverable and its claim label;
- the checked implication that would make success useful;
- a concrete stop condition, falsifier, or counterexample search;
- what the task explicitly does **not** claim about π or V1.

Tasks that cannot fill in these fields are too vague and should not run.

## Default operating model

Normal research runs use four clearly separated roles:

1. **Main operator:** one persistent oversight agent owns the run. It keeps the
   free workers supplied with bounded tasks, watches provider utilization and
   pod health, repairs general workflow failures, retires stale directions, and
   reports only material progress.
2. **Creative mathematics directors:** up to three maximum-intelligence Pro
   calls run in parallel on distinct hard questions at the current frontier.
   They read `FRONTIER.md`, the verified core, and the negative-result memory
   and return mathematical proof sketches only. They do not write Lean, edit
   the repository, design workflows, integrate results, or perform routine
   worker jobs.
3. **Knowledge integrator:** one subagent reviews returned artifacts,
   deduplicates them, preserves negative and intermediate findings, and
   prepares narrowly scoped candidates for the trusted core. It must prevent
   representation-only theorem volume from being mistaken for progress and
   integrate supported `GPTPro/` conclusions into the canonical knowledge
   hierarchy.
4. **Ox workers:** the free Ox Alpha providers perform high-volume bounded
   research inside isolated pods. Their output is untrusted input, never a
   result by itself. The current machine-wide ceilings are four concurrent
   OpenRouter `ox` calls and ten concurrent OpenCode `oxzen` calls.

Lean implementation, theorem registration, verification, and repository
integration are performed by the main operator and its local subagents, not by
the Pro directors. Pro and Ox output remains untrusted until that local path has
checked the exact statement and proof boundary.

Agents do not constitute the trust boundary. The operator may promote a formal
finding only after the independent kernel build, exploit scan, exact statement
contract, and axiom audit pass. The research director and knowledge integrator
must remain separate roles so choosing a direction, producing an artifact, and
accepting it are not one self-confirming step.

## Verify the core

```bash
lake build TheoryLib
pwsh workflows/verification/check.ps1
```

The gate rejects `sorry`, `admit`, `native_decide`, new axioms, opaque proof
declarations, unsafe declarations, and other compiler-trusting shortcuts.
Allowed foundational axioms remain exactly `propext`, `Classical.choice`, and
`Quot.sound`.

Computed examples remain `experiment` only. A formal research claim must also
have its exact theorem statement registered in `audit/AxiomAudit.lean` and must
match the prose claim quantifier by quantifier.

## Run one GPT Pro research turn

Give a capable model the prompt in [`GPTPro/PROMPT.md`](GPTPro/PROMPT.md). Each
invocation atomically claims one task through that task file's current Git blob
SHA, completes a bounded deliverable under `GPTPro/Deliverables/`, and closes
the task as `done` or `blocked`.

The main operator may also invoke Marcel's authenticated web ChatGPT Pro through
the `chatgpt-pro` skill for sharply bounded, hard creative-mathematics tasks.
Web Pro is a mathematician, not an operator. Reserve it for inventing or
stress-testing a genuinely difficult proof mechanism at one of the two active
quantitative frontiers. Do not spend it on orchestration, workflow or prompt
design, architecture audits, task selection, literature triage, computation,
extraction, formatting, integration, or repetitive checking.

There may be at most three active web-Pro calls at a time. Every prompt names the
repository, branch, exact mathematical gap, deliverable, checked usefulness
edge, stop condition, and claim boundary. The returned answer remains untrusted
external input until the knowledge integrator reviews it. If login/account
resumption, a browser permission, or a capacity warning blocks the call, stop
it and notify Marcel rather than guessing credentials or starting a second
call.

## Run the sandboxed Ox workflow

```bash
.venv/bin/python workflows/modelbench/runner.py \
  --sandbox \
  --sandbox-image localhost/allmath-research:latest \
  --tasks-dir workflows/modelbench/tasks/pi/current \
  --models ox,oxzen \
  --concurrency 20 \
  --out workflows/state/runs/pi-current
```

The runner enforces the provider ceilings itself; the larger feeder pool
prevents threads waiting for one provider from starving free slots at the
other. All model work runs in pods; only artifacts that independently pass the
Lean and axiom gates may enter `TheoryLib/`.

See [knowledge/pi/README.md](knowledge/pi/README.md) for the research-state map,
[workflows/README.md](workflows/README.md) for workflow operations, and
[GPTPro/README.md](GPTPro/README.md) for pro-model coordination.
