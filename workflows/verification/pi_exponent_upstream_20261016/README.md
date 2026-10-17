# Native verification of the pinned upstream π exponent claim

Status: `experiment` until the native workflow passes. This directory prepares
an isolated build of `openai/math` family 017 and checks its actual Lean
declarations. It does not import that library into PI.

## Fixed inputs

| Input | Pin |
| --- | --- |
| Upstream repository | `openai/math` |
| Upstream commit | `1581d4cbdd69a0faf34b2089614fe2a814316a6a` |
| Solution module | `OAI.NumberTheory.PiExponent.Main` |
| Native Lean toolchain | `leanprover/lean4:v4.34.1` |
| Mathlib commit | `d13f23b723b8a846827a245b89c10fc7d3f11612` |
| Proof import closure | 869 upstream modules |
| Permitted axioms | `propext`, `Classical.choice`, `Quot.sound` |

The [upstream statement](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/NumberTheory/PiExponent/Main.lean)
asserts an eventual lower bound with exponent `ν > 2` and irrationality
exponent exactly two. The upstream
[Comparator challenge](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/ComparatorChallenges/PiExponent.lean)
contains the expected statement and an intentional `sorry`; it is never
copied into or imported by this build.

## What the workflow checks

`prepare` starts from a checkout at the exact upstream commit. It follows
imports from the solution module, checks every copied proof file against its
Git blob at that commit, and requires the expected 869-module closure to
equal the complete PiExponent source subtree. The
only accepted external imports are root `Mathlib`, its submodules, and
`Lean.Elab.Tactic.Omega`. A comment-aware source scan rejects proof shortcuts
and explicit extra axioms. This scan is a supplementary guard, not a complete
Lean parser or a proof checker.

The native `lean-toolchain`, `lake-manifest.json`, and `lakefile.lean` are also
checked against their pinned Git blobs. A minimal Lake configuration replaces
the upstream configuration in a separate build directory. It preserves
`fixedToolchain := true`, `autoImplicit := false`, the Mathlib revision, and
the eight exact Mathlib dependency pins carried by the upstream manifest.
The unrelated upstream package graph and its compatibility-patch hooks are
not executed. No proof source is edited.

The workflow then builds `OAI.NumberTheory.PiExponent.Main` with its native
Lean release and runs `leanchecker` on the `OAI.NumberTheory.PiExponent`
module prefix. GitHub caches for upstream proof objects are disabled; the
standard Mathlib dependency cache remains enabled. Both compilation and the
kernel recheck are required workflow steps.

`PiExponentGate.lean` repeats the natural-denominator and integer-denominator
lower bounds and the full irrationality-exponent statement literally in
`#check` commands. It also checks the Flint Hills summability consequence.
It requests transitive axiom reports for these four declarations:

- `OAI.PiExponent.main`
- `OAI.PiExponent.pi_eventual_lower_bound`
- `OAI.PiExponent.pi_irrationalityExponent_eq_two`
- `OAI.PiExponent.flint_hills_summable`

`finish` requires exactly one complete report per declaration and fails on a
missing, duplicate, malformed, unexpected, or disallowed-axiom report. It
checks the source files, isolated build configuration, toolchain, dependency
manifest, actual dependency revisions, and tracked dependency changes before
and after running the literal statement and axiom gate. Seven Python tests
exercise the report parser and source-scan failure paths.

The workflow preserves a JSON report, the axiom log, and the isolated build
configuration and statement gate. The JSON report marks
the prepared stage separately from the completed statement/axiom checks.
Its kernel-recheck field points to the separate required workflow step;
reading a prepared report alone is not evidence of a successful verification.

## Running the same checks

Clone the upstream source at the fixed commit into a directory outside the
isolated build directory. The checkout must include the PiExponent subtree
and the three native build metadata files listed above. From the PI root:

```sh
python3 workflows/verification/pi_exponent_upstream_20261016/test_verify.py
python3 workflows/verification/pi_exponent_upstream_20261016/verify.py prepare \
  --upstream /absolute/path/to/upstream-math \
  --build workflows/state/pi-exponent-upstream/build \
  --report workflows/state/pi-exponent-upstream/report.json
```

With Elan installed, enter the isolated build directory and run:

```sh
lake exe cache get
lake build OAI.NumberTheory.PiExponent.Main
lake env leanchecker OAI.NumberTheory.PiExponent
```

Then, from the PI root:

```sh
python3 workflows/verification/pi_exponent_upstream_20261016/verify.py finish \
  --upstream /absolute/path/to/upstream-math \
  --build workflows/state/pi-exponent-upstream/build \
  --report workflows/state/pi-exponent-upstream/report.json
```

The build directory must be absent or empty for `prepare`; use a fresh
directory for a new run. The GitHub workflow performs the same stages and
uploads the reports, including partial reports after failure.

## Verification boundary

A successful run checks these pinned external declarations under their
native Lean and Mathlib versions. It does not port the result into PI's
different pinned environment, alter PI's axioms or dependency graph, or
discharge a PI theorem that still takes an irrationality-measure hypothesis.
Comparator and Nanoda are not run by this workflow. The literal `#check`
commands check the displayed statements directly; `leanchecker` supplies the
native kernel recheck, not an independent checker implementation.

The irrationality exponent alone supplies no prescribed decimal target sign.
No result here proves V1, CW0, CW9, or endpoint recurrence, and a green
verification run must not be presented as a digit-occurrence proof.
