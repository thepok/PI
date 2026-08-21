# GP-0002 — post-T17 cancellation criterion

## Result

The repository now contains the candidate theorem

```text
Theory.PiDigits.T110PostT17CancellationCriterion.
  C1_of_tail_aggregatedFourierSum_lt_of_powerTenDiophantine
```

in

```text
TheoryLib/PiQuantitativeBlockHitting/
  T110T110PostT17CancellationCriterion.lean
```

For fixed natural parameters `mu`, `A`, `C`, and `K`, it retains the exact
external premise

```text
PowerTenDiophantine Real.pi mu A
```

and assumes `1 <= mu`, `1 <= C`, and the strict upper bound below at every
admissible scale in the tail `K <= k`, `A <= k`, `1 <= k`:

```text
q = 10^k
D = C*k*q
N = D-k+1
r = (mu-1)*D+1
M = 2*10^(2*k+r)

aggregatedFourierSum piFractionalOrbit N q M < N/(2*q).
```

It concludes literal `C1`.

The proof is the direct strict contrapositive of T17.  Assuming `not C1`, T17
is invoked with lower threshold `max K 1`.  It returns a scale `k` satisfying
all three guards and

```text
N/(2*q) <= aggregatedFourierSum piFractionalOrbit N q M.
```

The tail upper bound at that same `k` contradicts this lower bound.

## Quantifier audit

An upper bound merely holding on an unbounded set of scales is **not** enough.
T17 only supplies another unbounded set of lower-bound scales, and two
unbounded subsets of the naturals can be disjoint (for example, even and odd
scales).

More sharply, suppose the only information used about T17's witness scales is
that they form an unbounded subset of the admissible tail.  A set of upper-bound
scales intersects every such unbounded witness set exactly when its complement
inside the admissible tail is bounded.  On the naturals, that is equivalent to
the upper bound holding at every sufficiently large admissible scale.  Thus the
tail hypothesis in T110 is the logically minimal generic set-of-scales
criterion available from T17 alone.  Any weaker useful condition would have to
exploit additional structure of the T17 witness set that T17 does not provide.

Strict `<` is also essential for this direct contradiction.  Replacing it by
`<=` would be compatible with equality at the T17 threshold.

## Dependency and trust audit

All dependencies remain explicit:

- `mu` controls `r = (mu-1)*D+1` and must satisfy `1 <= mu`.
- `A` is the onset in `PowerTenDiophantine`; T17 and T110 use only scales
  satisfying `A <= k`.
- `C` fixes `D = C*k*10^k` and must satisfy `1 <= C`.
- `K` is the cancellation onset; it may be zero because T17 is called at
  `max K 1`.
- `k`, `q`, `D`, `N`, `r`, and `M` are otherwise exactly T17's parameters.

GP-0001 separately established, at the literature-audit tier, that the pinned
Salikhov statement supports an external proposition of the form

```text
exists A >= 1, PowerTenDiophantine Real.pi 8 A.
```

The source statement does not expose a numerical threshold `A`, and no such
literature fact has been inserted as a Lean axiom.  T110 therefore correctly
retains `hpi` as an explicit kernel-level premise.

No model output, finite computation, literature summary, or successful Lean
build is being treated as a proof of the repository's main decimal-disjunctivity
claim.  T110 is only a conditional reduction.

## Duplicate audit

The existing T17 endpoint proves a lower bound under `not C1`; T18 and later
modules pursue other resonance refinements.  No existing audited theorem was
found that packages this exact strict tail contrapositive with T17's full
parameter definitions and external Diophantine premise.

## Repository changes

- `TheoryLib/PiQuantitativeBlockHitting/T110T110PostT17CancellationCriterion.lean`
  — theorem and local `#print axioms` command.
- `GPTPro/Deliverables/GP-0002/promote_t110.py` — deterministic, idempotent
  helper that inserts the canonical `TheoryLib.lean` import and central
  `audit/AxiomAudit.lean` import/registration without replacing concurrent
  repository content.
- `.github/workflows/gptpro_gp0002_verify.yml` — temporary self-reporting
  verification harness necessitated by the absence of `lean`, `lake`, and
  `pwsh` in the invocation runtime and by the GitHub connector's inability to
  read push-run logs.  It is to be removed after committed verification
  evidence exists.
- `GPTPro/Deliverables/GP-0002/CI_VERIFICATION.md` — generated verification
  transcript; pending at the time of this draft.

Initial theorem commit:

```text
24953b999b9a8638834b35268a588b86e8ab13e9
```

## Verification protocol

The self-reporting workflow first runs the isolated target:

```text
lake build \
  TheoryLib.PiQuantitativeBlockHitting.T110T110PostT17CancellationCriterion
```

Only after that succeeds does it apply the idempotent canonical registration
and run the repository's exact strict gate:

```text
pwsh workflows/verification/check.ps1
```

That gate rebuilds the canonical `TheoryLib` target, scans the verified track
for forbidden shortcuts, recompiles `audit/AxiomAudit.lean`, and rejects every
axiom outside `propext`, `Classical.choice`, and `Quot.sound`.

Final exit codes, the exact commit under test, the tail of both command logs,
and the target theorem's printed axiom dependencies are recorded in
`CI_VERIFICATION.md`.  This README will be finalized only after that evidence
is present.

## Rejected shortcuts

- Replacing the tail hypothesis by an arbitrary unbounded-set hypothesis.
- Weakening the strict upper bound to a non-strict inequality.
- Hiding or postulating the external `PowerTenDiophantine` premise.
- Treating GP-0001's literature audit as a kernel theorem.
- Calling an isolated green build a proof of `C1` or of the main claim.

## Remaining bottleneck

The unresolved mathematical bottleneck is an actual deterministic estimate
showing the displayed strict aggregated-Fourier upper bound for the fixed pi
orbit on an admissible tail.  T110 identifies the target exactly but supplies
no cancellation estimate.
