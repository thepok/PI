# GP-0002 — post-T17 cancellation criterion

**Claim label:** machine-checked

## Verdict

The sharp clean consequence of T17 is an **eventual admissible-tail**
criterion, not an arbitrary unbounded-set criterion.

A provenance copy of the Lean candidate is retained at:

```text
GPTPro/Deliverables/GP-0002/T110Candidate.lean
```

It defines:

```text
Theory.PiDigits.T110PostT17CancellationCriterion.
  C1_of_tail_aggregatedFourierSum_lt_of_powerTenDiophantine
```

The independently verified canonical theorem is now present at
`TheoryLib/PiQuantitativeBlockHitting/T110T110PostT17CancellationCriterion.lean`,
imported by `TheoryLib.lean`, and registered in `audit/AxiomAudit.lean`.

## Exact result

For fixed natural parameters `mu`, `A`, `C`, and `K`, retain the external
premise

```text
PowerTenDiophantine Real.pi mu A
```

and assumptions `1 <= mu` and `1 <= C`. Suppose that for every `k` satisfying

```text
K <= k,  A <= k,  1 <= k,
```

with T17's exact definitions

```text
q = 10^k
D = C*k*q
N = D-k+1
r = (mu-1)*D+1
M = 2*10^(2*k+r),
```

one has

```text
aggregatedFourierSum piFractionalOrbit N q M < N/(2*q).
```

Then `C1` follows.

The proof is the strict contrapositive of T17. Assuming `not C1`, invoke T17
with lower threshold `max K 1`. It returns one scale `k` satisfying all three
guards and

```text
N/(2*q) <= aggregatedFourierSum piFractionalOrbit N q M.
```

The assumed strict upper bound at that same scale is contradictory.

`K` need not be positive. The call at `max K 1` supplies T17's positivity
requirement while still giving `K <= k`.

## Quantifier sharpness

An upper bound on merely an unbounded set of scales is insufficient. T17 gives
an unbounded set of lower-bound scales, and two unbounded subsets of the
naturals can be disjoint; even and odd scales are the elementary example.

More precisely, if the only available information about T17's witness scales
is that they form an unbounded subset of the admissible scales, then a set of
upper-bound scales is guaranteed to meet every possible witness set exactly
when its complement within the admissible scales is bounded. Over the
naturals, that is equivalent to containing an admissible tail. Hence the tail
hypothesis is the logically minimal generic set-of-scales condition obtainable
from T17 alone. A genuinely weaker sufficient condition would require new
structure on T17's witness set.

The inequality must be strict. A non-strict upper bound is compatible with
equality at T17's threshold.

## Dependency and trust audit

Every parameter remains visible:

- `mu` controls `r = (mu-1)*D+1` and satisfies `1 <= mu`;
- `A` is the exponent onset in `PowerTenDiophantine` and appears as `A <= k`;
- `C` fixes `D = C*k*10^k` and satisfies `1 <= C`;
- `K` is the cancellation onset;
- `k`, `q`, `D`, `N`, `r`, and `M` are exactly T17's quantities.

GP-0001 separately concluded at the literature-audit tier that the pinned
Salikhov statement supports an external proposition of the form

```text
exists A >= 1, PowerTenDiophantine Real.pi 8 A.
```

The source does not expose a numerical `A`. No literature statement was added
as a Lean axiom. This candidate therefore retains `hpi` as an explicit premise.

The result is only a conditional reduction. It is not evidence that the
required cancellation estimate is true, and it proves neither the main decimal
claim nor an unconditional instance of `C1`.

## Duplicate audit

T17 exposes the lower bound under `not C1`. T18 and later modules package other
resonance refinements. No existing theorem was found that states this exact
strict tail contrapositive with T17's complete parameter definitions and the
external Diophantine premise intact.

## Deliverables and repository changes

- `GPTPro/Deliverables/GP-0002/T110Candidate.lean` — exact Lean candidate and
  local `#print axioms` command.
- `TheoryLib/PiQuantitativeBlockHitting/T110T110PostT17CancellationCriterion.lean`
  — independently compiled canonical theorem.
- `knowledge/pi/results/machine-checked/t110_post_t17_tail_cancellation_criterion_20260821.md`
  — integrated result and claim boundary.
- `GPTPro/Deliverables/GP-0002/README.md` — result, quantifier audit, trust
  classification, verification record, and promotion history.

An initial canonical-track draft was committed at
`24953b999b9a8638834b35268a588b86e8ab13e9` solely to attempt execution through
repository CI. The late CI report in `CI_VERIFICATION.md` failed before
compilation because it tested commit `27669ba`, where the canonical T110 file
did not exist; this is not a candidate compile failure and supplies no positive
verification evidence. The draft was removed from `TheoryLib` in
`000fbb0fab5cb4005b441a5ab936c9dffa94441d`.
The temporary self-reporting workflow was removed in
`e9c66e9dc44debb57faca8532e94393b0585eb29`. No temporary workflow or
unverified canonical theorem remains.

## Verification performed

### Exact T17 interface audit — PASS

The candidate was checked against
`T17T17PowerTenDiophantineReduction.lean`:

- T17 returns `K <= k`, `A <= k`, and `1 <= k`;
- after its local definitions, the result has exactly eight conjunction
  components;
- the final component is the required lower bound with the same `N`, `q`, and
  `M`;
- the candidate destructures that exact conjunction and contradicts it with
  `not_lt_of_ge`.

### Static candidate trust scan — PASS

The staged source contains all five exact parameter definitions, the expected
T17 endpoint, the explicit `PowerTenDiophantine` premise, and the local
`#print axioms` command. It contains none of:

```text
sorry
admit
native_decide
unsafe
axiom
```

This is a source check, not a Lean compilation result.

### Promotion helper checks — PASS

Executed locally:

```text
python3 -m py_compile promote_t110.py
```

Outcome: exit `0`.

A mock-repository test also passed:

- first run installed the candidate and all registrations;
- second run reported no changes;
- a divergent existing canonical T110 caused exit `1` with an explicit refusal
  to overwrite it.

### Lean and repository verification gate — PASS

The main operator independently compiled the staged candidate, promoted a
clean canonical module, and ran `pwsh workflows/verification/check.ps1` on
2026-08-21. The full 8,766-job kernel build, forbidden-marker/exploit scan,
and exact-allowlist axiom audit passed. The registered theorem depends only on
`propext`, `Classical.choice`, and `Quot.sound`.

## Promotion result

Promotion is complete. The one-use promotion helper was removed after the
canonical module and audit registration passed the full gate, avoiding stale
operational machinery that could later diverge from the canonical source.

## Rejected alternatives

- Replacing the tail hypothesis by an arbitrary unbounded-set hypothesis.
- Weakening `<` to `<=`.
- Hiding or postulating `PowerTenDiophantine Real.pi mu A`.
- Treating GP-0001's literature audit as a kernel theorem.
- Leaving an uncompiled module in the canonical verified track.
- Calling a static audit or a green build a proof of the main claim.

## Remaining bottleneck

The actual mathematical bottleneck is much harder: prove the
displayed strict aggregated-Fourier upper bound for the fixed pi orbit on an
admissible tail. GP-0002 identifies that target exactly but contributes no
cancellation estimate.
