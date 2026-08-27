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

The sole active research branch is `main`. Read and target `main` directly;
do not create side branches unless the main operator explicitly requests one.

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
T129 exacts both zero modes and proves that boundary matching gives a strictly
larger signed zero mode for every `q > 1`. T130 checks the full piecewise cubic
cross-determinant algebra and the actual normalized improvement at the outer
frequency `2q-1`. Identifying every actual interior frequency fiber with the
cubic formula is now machine-checked in T131. The remaining finite transfer to
the full actual normalized nonzero-coefficient comparison is now closed in
T132 by an exact signed edge-fiber formula. The genuine `q=10` separators
are now split: T133 machine-checks the directional Boundary-vs-Jackson
separator, and T134 machine-checks the larger 26-point aggregate separator.
The fixed-pi premise remains open.

The current unconditional fixed-frequency results give only additive gaps and
do not approach this moving-frequency normalized estimate. Future Fourier work
must bound the actual directional or aggregated quantity on the growing
natural-scale frequency window, strictly weaken this sufficient premise, or
rigorously prove that a proposed route cannot do so.

Two audited `proof sketch` transfer analyses sharpen what such work must
retain. The
[transfer-compatible directional family](knowledge/pi/results/intermediate/20260824-transfer-compatible-directional-kernel.md)
has an exact decimal preimage law but shows that parent positivity cannot force
all prescribed children. The
[boundary carry-flow identity](knowledge/pi/results/intermediate/20260824-boundary-kernel-carry-flow.md)
isolates the missing input as a carry-corrected predecessor-digit correlation;
successor-only scalar transport and exact finite-polynomial telescoping are
insufficient. Neither note supplies the missing fixed-π estimate.

T169 now machine-checks a second exact rational-carrier bridge: throughout the
natural window `|h| < 2*10^k`, the decimal pi phases can be replaced by the
single-rate Machin phases `10^n * machinLower(n+k)` with geometric ratio
`10/625` and an error uniform in every nonempty horizon. An independently
audited [`proof sketch`](knowledge/pi/results/negative/20260825-high-prime-bbp-matching-complement-no-go.md)
also shows that the currently exposed T159--T166 high-prime BBP pole sector,
once its matching complementary factors are retained, changes the complete
target-signed score by only `O((5/64)^m/m)`. This retires separate averaging of
those known prime coordinates, not joint low-prime or complementary-carrier
arguments. Neither result supplies the still-open fixed-pi signed cancellation
estimate.

### 2. Moving-mesh occupancy-tail and canonical entropy targets

For a selected block `[L, 2L)` and a partition into `q` equal cells, let `n(a)`
be the number of orbit points in cell `a`. For arbitrary moving meshes, the
weakest reviewed Haar consumer currently asks for uniform integrability of the
cell-smoothed densities:

```text
lim_(M→∞) sup_j (1/L_j)
  ∑_{a : n_j(a) > M L_j/q_j} n_j(a) = 0.
```

Together with `L_j,q_j→∞` and vanishing averaged pseudo-orbit error, this tail
condition forces selected-block Haar limits and hence fixed-cylinder hits. The
older collision second-moment bound and the intermediate bounded-entropy-
deficit premise both imply this condition; reviewed exact decimal de Bruijn
stages separate the converses.

On exact consecutive decimal-orbit blocks and canonical `10^k` meshes, there is
a still weaker audited `proof sketch` premise: sublinear Shannon-entropy deficit
`k * log 10 - H_k = o(k)`. Finite entropy stationarization then forces every
fixed-depth cell law to converge in total variation to uniform, hence the
selected empirical measures converge to Haar and V1 follows. Canonical-mesh
uniform integrability implies this sublinear deficit, and an exact global de
Bruijn separator shows that the implication is strict.

These consumers and separators are currently `proof sketch`; more importantly,
neither the displayed tail estimate nor the sublinear canonical entropy estimate
is proved for the decimal π orbit or the sampled BBP orbit. The valuable work is
to prove, sharpen, or falsify one of those fixed-π premises, not to restate a
consumer.

Effective irrationality alone is now decisively excluded as a route to this
tail premise: an audited sparse-decimal seed has irrationality exponent at
most `3`, satisfies an explicit exponent-`4` effective bound, and nevertheless
fails UI on every moving-mesh selection. T126 machine-checks its local
zero-window-to-first-cell mechanism; the full separator remains `proof sketch`.

### Priority order

The current research cycle is not primarily another attempt to derive V1 from
the existing BBP, Machin, p-adic, irrationality, or generic-dynamical library.
Those routes repeatedly supply local structure, denominators, periods,
magnitudes, or almost-everywhere statements while losing the Archimedean,
target-dependent sign of the actual pi orbit.  The new priority is to build a
small pi-specific bridge theory around precisely that missing information.

Its provisional summit is

```text
forall k >= 3, forall A < 10^k, exists N >= 10^k:
  Re (primitiveBoundaryFourierSum (10^k) A N) >= 0.
```

An explicitly stronger theorem or a theorem with a shorter checked path to V1
is equally acceptable.  Work backward from that summit.  For every proposed
lemma ask: **where does its target-signed Archimedean information about the
actual constant pi come from?**  Symmetry, averaging, almost-everywhere
behavior, denominator size, periodicity, local congruences, unsigned energy,
or a rational shadow do not answer that question by themselves.

1. Establish the first rigorous lemma of this pi-specific signed bridge
   theory: a new invariant, recurrence, drift, energy, or special-arithmetic
   estimate that retains the complete target information.
2. Use PaperSearch early to find mathematical components that may generate
   that information, without restricting invention to standard literature
   routes.
3. Prove or sharply falsify the critical signed step of the best surviving
   candidate before multiplying representations or consumers.
4. Formalize a representation or external theorem only after a concrete
   argument shows how it supplies a named signed consumer bound.
5. Use computation to kill bad conjectures early, never as evidence that the
   required pointwise statement holds for pi.

The first finite rung of this program is now concrete but deliberately
limited. A directed-interval `experiment` proves numerically that

```text
Re (primitiveBoundaryFourierSum 1000 334 10000) > 47539 / 2500.
```

The replay uses the exact Chudnovsky-certified prefix and the complete
T128/T139 kernel-plus-endpoint identity; see
[`20260827-finite-signed-parent-334-certificate.md`](knowledge/pi/results/intermediate/20260827-finite-signed-parent-334-certificate.md).
T170 separately machine-checks a 100-decimal-place fixed-point Machin
enclosure as the first Lean feasibility rung. T171 replaces its direct
rational normalization by a compact integer-row checker, and T173 scales that
checker to a machine-checked 10,015-fractional-place cylinder for pi: 14,341
rows at scale `10^10021`, checked in about 41 seconds with about 9.6 GB peak
memory in the focused audit. This supplies enough trusted decimal information
for the finite score calculation. T180 now supplies the small trusted analytic
core of the next certificate rung: mathlib's complex-exponential remainder
bound, simultaneous reflected sine/cosine intervals, input-width transport,
and an integer-checked rational-sum certificate. The full generated `q=1000`,
`N=10000` path is now also implemented semantically: T181 checks common-scale
interval arithmetic, T182 proves one stack-program interpreter sound, T183
uses compact fixed-point Horner evaluation, T184 certifies reduced actual-pi
phase requests from the T173/T175 cylinder, and T185 reconnects the closed
sine kernel to the literal T174 score. A benchmark rejected exact Taylor
powers (about 39 GB projected) and selected roughly 16 MB of Horner payload in
small shards instead. The generated numerical payload itself is still
missing, so the root-score claim remains an `experiment`. A fail-fast replay
using exactly the T173/T175 information boundary (no digit after fractional
place 10,015) still leaves a lower margin `>2.36886869e-5`, with total interval
width below `2.40e-13` and no denominator crossing. Thus the existing trusted
prefix is sufficient for the planned payload. None of these finite results
supplies an unbounded-scale signed mechanism or advances the claim status of
V1.

T172 now machine-checks the exact ten-child zero-character transport, strict
positivity of every coefficient defect, and total defect mass
`<21/(10q^2)`. With the finite actual-pi seed this gives a rigorously audited
positive-score predecessor ray at unbounded decimal scales, but at the fixed
horizon `N=10000`. It selects only one existential leading digit per level;
after the first child the horizon is below the scale, so no current checked
consumer turns the ray into new occurrences. The next mathematical rung is
therefore not another coefficient identity: it is horizon-growing actual-pi
sign control or a prescribed nonzero predecessor-character estimate.

T176 and T177 make that boundary exact. T176 proves the strict block Bellman
surplus with potential `7/(3q)`; T177 Fourier-resolves all ten predecessor
digits, proves exact inversion, and isolates nine mean-zero nonzero-character
corrections. A specified next digit now has one named missing signed quantity
rather than an informal appeal to "child phases." T178 machine-checks the
conditional infinite recursive ray and its explicit all-level lower bound,
leaving only the finite root-score certificate outside Lean. T179 then
rewrites every nonzero character sector exactly as an actual-pi lag-one
correlation between the predecessor digit and the next suffix. The remaining
gap is therefore a genuine one-sided arithmetic estimate for these explicit
correlations, not another transport or DFT identity.

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

Research uses four clearly separated roles when the relevant resources are
enabled:

1. **Main operator:** one persistent oversight agent owns the run. It keeps
   enabled resources focused on the live frontier, monitors active work,
   retires stale directions, and reports only material progress.
2. **Creative mathematics directors:** up to three maximum-intelligence Pro
   calls run in parallel on distinct hard questions in the pi-specific signed
   bridge program.
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
4. **Ox workers (currently stopped):** when explicitly re-enabled by the
   operator, the free Ox Alpha providers may perform high-volume bounded
   research inside isolated pods. Their output is untrusted input, never a
   result by itself. Operator direction currently forbids launching this work;
   the configured ceilings remain four concurrent OpenRouter `ox` calls and ten
   concurrent OpenCode `oxzen` calls for a future authorized run.

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

Persistent web-Pro operating rules are collected in
[`GptProGuide.md`](GptProGuide.md); the operator must read it before launching
or continuing a Pro call.

Give a capable model the prompt in [`GPTPro/PROMPT.md`](GPTPro/PROMPT.md). Each
invocation atomically claims one task through that task file's current Git blob
SHA, completes a bounded deliverable under `GPTPro/Deliverables/`, and closes
the task as `done` or `blocked`.

The main operator may also invoke Marcel's authenticated web ChatGPT Pro through
the `chatgpt-pro` skill for relatively open but progress-gated hard
creative-mathematics tasks.
Web Pro is a mathematician, not an operator. Reserve it for inventing or
stress-testing a genuinely difficult proof mechanism at an active quantitative
frontier. Do not spend it on orchestration, workflow or prompt
design, architecture audits, task selection, literature triage, computation,
extraction, formatting, integration, or repetitive checking.

There may be at most three active web-Pro calls at a time. Give each call a
small current frontier packet directly in the prompt: the GitHub `main` link,
the exact V1 statement, one named open pi-arithmetic transition, three to five
direct `main` links, and a short list of the relevant recorded separators. Do
not ask a Pro model to map the repository or edit it. Require a self-contained
mathematical memo containing a genuinely new theorem, estimate, structural
identity with quantitative force, or decisive no-go—not a reformulation.

Treat that packet as a starting compass, not a closed reading list. Permit the
model to follow a small number of mathematically motivated repository links or
primary literature sources when they may unlock the argument. Keep the prompt
open: state the hard boundary and the progress test, but do not prescribe a
long method sequence or enumerate every forbidden construction. Mention only
the few separators that would otherwise cause an immediate duplicate. A Pro
memo should be judged afterward by independent audit, rather than steered into
proving a narrow no-go for an operator-invented mechanism.

Keep the three creative slots differentiated by default:

1. invent a signed invariant, recurrence, or energy/drift structure that
   preserves the complete target information;
2. seek a special pi-arithmetic input—from integrals, Padé/hypergeometric or
   special-function theory, modular structure, or another promising source—
   that could control that invariant;
3. work adversarially on the strongest current candidate by proving its
   critical step or destroying it with a narrow separator.

The roles are mathematical compasses, not closed method lists. When a memo
survives local audit, use the next call to attack its strongest remaining step
instead of restarting a broad search. The returned answer remains untrusted
external input until the knowledge integrator reviews it. If login/account
resumption, a browser permission, or a capacity warning blocks the call,
notify Marcel immediately rather than guessing credentials or starting a
duplicate call. Do not cancel an active Pro task; allow it to reach its own
terminal state.

End each web-Pro memo with a compact attempt ledger covering every substantive
route tried during that turn, not only the route selected for exposition. For
each route give the proposed lemma or mechanism, its first fatal line (or the
surviving open step), and the genuinely new ingredient that would be required
to reopen it. The operator audits and deduplicates those entries into
[`GPTPro/ATTEMPT_LEDGER.md`](GPTPro/ATTEMPT_LEDGER.md). Future prompts should
quote only the few ledger entries relevant to that run: enough to prevent
repetition without turning the ledger into a closed list of permitted ideas.

## Paused sandboxed Ox workflow

Ox research is stopped by current operator direction. Do not run the command
below unless Marcel explicitly re-enables Ox work; it is retained only as the
reproducible invocation for a future authorized run.

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
