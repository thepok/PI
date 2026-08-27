# T70 infinite-support extension: independent adversarial audit

Audit date: **2026-08-13 UTC**.

Canonical target: [problems/local/pi-digits.txt](../../problems/local/pi-digits.txt),
SHA-256
`2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825`.

Audited module:
[T70T70EmpiricalRigidityBridge.lean](../../TheoryLib/PiQuantitativeBlockHitting/T70T70EmpiricalRigidityBridge.lean),
SHA-256
`f3798779a55a280d43e98ea5324c7cc0bdf18f7b8648a6b4e3a1352e7ccf9a3e`.

Independent artifacts:

- [t70_infinite_support_independent_checks.lean](t70_infinite_support_independent_checks.lean),
  SHA-256
  `23cc27b8a679405190f0f467958897f64228cde921d08ff4f433c92201f2301f`;
- [t70_infinite_support_independent_check.py](t70_infinite_support_independent_check.py),
  SHA-256
  `fff4b5d9def83a887f5c7b1df949ff0ac655d9ab8a947643e83682fecadae046`.

## Verdict

**PASS — `machine-checked` conditional bridge.**

The new support, compact-set, and V1 implications have the stated semantics.
The one-sided absolute-continuity direction is correct, the rational
difference-set case is valid, and every use of the two Furstenberg conclusions
is routed through an explicit argument of type `FurstenbergSourcePremise`.
No inhabitant of that structure is constructed anywhere under `TheoryLib/`.

This is not an unconditional proof of V1.  It proves only implications whose
unresolved hypotheses remain visible in their theorem signatures.  In
particular, the module does not construct a pi empirical limit and does not
prove infinite support, times-sixteen absolute continuity, or times-sixteen
nonsingularity for such a limit.  Canonical V1 remains a `conjecture`.

## Adversarial semantic checks

### 1. Support and absolute-continuity direction

`support_mapsTo_of_continuous_map_absolutelyContinuous` assumes

\[
  f_*\mu \ll \mu,
\]

not the reverse direction.  For (x\in\operatorname{supp}\mu), continuity
makes the inverse image of every open neighborhood of (f(x)) an open
neighborhood of (x).  It therefore has positive (mu)-measure, so the
original neighborhood has positive (f_*\mu)-measure.  Thus
(f(x)\in\operatorname{supp}(f_*\mu)).  The standard support monotonicity
lemma for (f_*\mu\ll\mu) then gives

\[
  \operatorname{supp}(f_*\mu)\subseteq\operatorname{supp}\mu.
\]

The composite conclusion (f(\operatorname{supp}\mu)\subseteq
\operatorname{supp}\mu) is consequently in the correct direction.  The
independent Lean restatement pins this exact type.

### 2. Compact invariant-set dichotomy

For an infinite compact (K\) forward invariant under multiplication by 10
and 16, the proof splits exhaustively.

- If (K\) contains an irrational circle point, the first field of
  `FurstenbergSourcePremise` makes its joint \(10^s16^t\)-orbit dense.  Forward
  invariance puts that orbit in (K\), and closedness of compact (K\) yields
  (K=\mathbb T\).
- If every point of (K\) is rational, compactness and infinitude make zero an
  accumulation point of (K-K\).  Both forward invariances pass to (K-K\).
  The second field of `FurstenbergSourcePremise` therefore yields
  (K-K=\mathbb T\).  But every difference of two rational circle points is
  rational, whereas \(\sqrt2\bmod1\) is not.  This is a contradiction.

The maps used by the source premise are definitionally the same circle maps
as T70's `timesTenMap` and `timesSixteenMap`; the conversions do not reverse a
`MapsTo` relation.  The rational case does not assume that an infinite set of
rational points is closed: compactness is an explicit hypothesis and is used
to obtain the accumulation point.

### 3. Scope of the source premise

The premise is a `Prop`-valued structure in T77 with exactly two fields:
irrational joint-orbit density and the zero-accumulation invariant-set lemma.
T70 takes it as an ordinary theorem parameter in every new result that uses
it.  A repository-wide declaration scan found its sole declaration and no
`def`, theorem, lemma, instance, axiom, opaque declaration, or constant whose
result type is `FurstenbergSourcePremise`.

Accordingly, Lean's reported axiom dependencies do not include a new source
axiom.  This does not mean that Furstenberg's theorem has been formalized: the
mathematical source result is still an explicit external premise supplied by
the caller.

### 4. The two V1 bridges

The ergodic bridge assumes a probability measure, times-ten ergodicity,
support inside the pi decimal-orbit closure, non-mutual-singularity with the
times-sixteen pushforward, infinite support, and the source premise.  T39's
ergodic dichotomy gives equality of the two measures in the correct direction;
the resulting common support invariance and the compact-set theorem give full
support.  Full support inside the closed pi orbit closure makes that closure
the whole circle, and T69 converts exactly that statement to list-valued V1.

The nonergodic bridge instead assumes exact times-ten invariance and
((T_{16})_*\mu\ll\mu\).  It uses only support invariance and therefore neither
assumes nor concludes equality with the times-sixteen pushforward.  It does
not need a probability normalization.  Infinite support and support inclusion
remain explicit.  The same topological final step is sound.

Neither theorem has a hidden default measure, dense point, source-premise
instance, or inferred proof of infinite support.

## Kernel and audit checks

The independent type-check file restates the exact interfaces rather than
merely checking declaration names.  It fixes the absolute-continuity
orientation and lists every unresolved hypothesis of both V1 conclusions.

The following commands succeeded:

```text
lake env lean TheoryLib/PiQuantitativeBlockHitting/T70T70EmpiricalRigidityBridge.lean
lake env lean work/ultrapi-resume/t70_infinite_support_independent_checks.lean
lake env lean audit/AxiomAudit.lean
python3 work/ultrapi-resume/t70_infinite_support_independent_check.py
```

The deterministic checker returned `PASS`.  It pinned the source, T77, T70,
and its independent Lean restatements; rejected forbidden proof mechanisms;
confirmed exactly one declaration and exactly one axiom-audit registration for
each new theorem; scanned for a hidden source-premise inhabitant; and rebuilt
the focused module, independent checks, and complete axiom audit.

All five independently printed extension theorems depend only on the existing
allowlist:

```text
propext
Classical.choice
Quot.sound
```

No `sorry`, `admit`, `native_decide`, new axiom, opaque or constant proof,
unsafe declaration, or compiler-trusting shortcut occurs in T70.  The only
focused compiler diagnostic was a deprecation warning for `push_neg`; it has
no semantic or trust impact.

The complete [AxiomAudit.lean](../../audit/AxiomAudit.lean) compiled at audit
time with SHA-256
`f14e39abaf169e652df09c022097bfd45f75c8236a5cadc25355a758164ff715`.
All six declarations introduced by the extension are registered exactly once.

## Dependency pins

| dependency | SHA-256 |
|---|---|
| T39 ergodic-affinity rigidity | `f4982dacc90a436ca14e52d0529acbbfa8067d47e80679fb0173dff559d2ba09` |
| T69 fixed-sixteen return / full-closure-to-V1 bridge | `fb7eb54d99bb904c28da0f49d33f8a40979ffcbf22a4024fcae73de7149886f9` |
| T77 source-premise and difference-set lemmas | `efa2fe46b508539891e00097a52fb9df6cd4c6bb958aa7e49a300c9450a4550c` |

## Limitations and claim boundary

The extension is a genuine reduction in the hypotheses needed at the
measure-to-topology stage: density of a separately supplied point is replaced
by infinite support, and exact times-sixteen measure invariance can be replaced
by one-sided pushforward absolute continuity.  But the fixed-pi bottleneck is
not discharged.  A future argument must still produce an applicable measure
and prove the relevant infinite-support and matching/nonsingularity facts.

Therefore the correct label is `machine-checked` for the conditional theorem,
while the assertion that every finite decimal word occurs in pi remains a
`conjecture`.
