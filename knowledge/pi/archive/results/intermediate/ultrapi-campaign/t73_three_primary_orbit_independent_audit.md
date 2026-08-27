# Independent formal audit: T73 three-primary orbit

Audit date: **2026-08-13 UTC**

## Verdict and claim boundary

**PASS on the frozen final snapshot.**  The nine theorem declarations in
[`T73T73ThreePrimaryOrbit.lean`](../../TheoryLib/PiQuantitativeBlockHitting/T73T73ThreePrimaryOrbit.lean)
compile with `--trust=0`, occur exactly once in
[`AxiomAudit.lean`](../../audit/AxiomAudit.lean), and report only
`propext`, `Classical.choice`, and `Quot.sound`.  Those are exactly the three
axioms permitted by the unchanged repository gate.  The full gate ended:

```text
PASS: kernel build, exploit scan, and exact-allowlist axiom audit succeeded.
```

The registered generic orbit statements are `machine-checked`.  They prove
the exact power-of-three period of ten and the complete isolated residual
coset.  They do **not** formalize the BBP denominator-epoch formula, the
depth-dependent multiplier \(\beta_M\), proportional row coverage, any other
CRT coordinate, a full BBP phase return, or a decimal word occurrence in pi.
Canonical V1 remains a `conjecture`; this audit is not a `candidate
resolution` or `verified resolution`.

## Frozen final inputs

| input | SHA-256 |
|---|---|
| [`problems/local/pi-digits.txt`](../../problems/local/pi-digits.txt) | `2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825` |
| [`T73T73ThreePrimaryOrbit.lean`](../../TheoryLib/PiQuantitativeBlockHitting/T73T73ThreePrimaryOrbit.lean) | `1499b29893a05fe91d64ee468ff320f0f59c23eb07f13220dab64b9fbfe23009` |
| [`AxiomAudit.lean`](../../audit/AxiomAudit.lean) | `26b5c4bdb4d13e2caeca2885fff6b7e4284c366f511a40033202d943328af6fa` |
| [`bbp_three_primary_epoch_20260813.md`](bbp_three_primary_epoch_20260813.md) | `5b34ceb3aa2857b9227cce5ac7ae84cafbbac47d2c12adf889c37f11280d6fd7` |
| [`bbp_three_primary_epoch_20260813_check.py`](bbp_three_primary_epoch_20260813_check.py) | `4cb663d1d484c750ad99d2120d13143c24297ab4f81860a9f1584d5018ea2fa1` |
| [`bbp_three_primary_epoch_20260813_independent_check.py`](bbp_three_primary_epoch_20260813_independent_check.py) | `c15ef949abc0d2f3f0cd7331bccd2fb8ecf0a4109142091427f1438aaafd9e8f` |
| [`scripts/check.ps1`](../../scripts/check.ps1) | `953387f14651d68915361ca5baf1514ed1d22a434e1d2b1d4d417df62d3271b3` |
| [independent Lean checks](t73_three_primary_orbit_independent_checks.lean) | `da35143093d1f77fd7b63592b1a66aab40223e12cf43fa29b1c471aba95d2cb7` |

The T73 header preserves the canonical local source path and its exact hash.
The target is Marcel's local human-authored question and has no external
source URL; none is invented here.  This audit did not edit T73,
`AxiomAudit.lean`, `TheoryLib.lean`, or `ultrapi.md`.

## 1. Concurrent-mutation incident and restart

The audit caught and rejected an untrusted intermediate edit.  Initial
inspection saw a nine-theorem T73 snapshot with SHA
`769b1dbb4a607839f448157bdb75fcc568b784fec213a48e5d8dd2bd7d7d9a47`.
While the first kernel replay was running, the shared file acquired two new
unfinished declarations, `residualCoset_ncard` and
`residualClass_range_eq_coset`.  Lean reported unresolved goals near lines
158, 160, 166, and 177, and `#print axioms` consequently displayed
`sorryAx` for both declarations.  No such state was accepted as evidence.

The parent agent confirmed that this was its own in-flight edit and removed
both incomplete declarations and their proposed audit entries rather than
carrying a placeholder forward.  The audit then restarted from the current
SHA `1499...`.  That final source has nine theorems, contains neither
unfinished declaration, and passes all checks below.  The incident is a
shared-worktree race warning, not a remaining defect in the frozen final
snapshot.

## 2. Exact formal surface

T73 defines only these three objects:

1. `tenUnit e`, the unit represented by ten in
   \(\mathbb Z/3^{e+2}\mathbb Z\);
2. `residualTen n = (10^n-16)/3` as an integer;
3. `residualClass e n`, its class modulo \(3^{e+1}\).

Its nine registered theorem declarations are:

1. `tenUnit_coe`;
2. `orderOf_tenUnit`;
3. `tenUnit_pow_eq_iff`;
4. `tenUnit_pow_injective_on_period`;
5. `three_mul_residualTen`;
6. `residualTen_mod_three`;
7. `residualClass_injective_on_period`;
8. `residualClass_range_ncard`;
9. `residualClass_cast_three`.

The core statements are, for every \(e,n,m\in\mathbb N\),

\[
 \operatorname{ord}_{3^{e+2}}(10)=3^e,
 \qquad
 10^n=10^m\pmod{3^{e+2}}
 \iff n\equiv m\pmod{3^e}.                         \tag{1}
\]

They also prove

\[
 3\,\operatorname{residualTen}(n)=10^n-16,
 \qquad
 \operatorname{residualTen}(n)\equiv1\pmod3,       \tag{2}
\]

and show that the first \(3^e\) residual classes modulo \(3^{e+1}\)
are distinct, number exactly \(3^e\), and all reduce to one modulo three.
The parameter boundary \(e=0\) is included: the period is one,
`residualTen 0 = -5`, and its class modulo three is one.

No positivity hypothesis on \(n\) is hidden.  This slightly strengthens the
report's \(n\ge1\) use and is harmless: (2) is true at zero as well.

## 3. Independent converse and coset checks

The [independent Lean harness](t73_three_primary_orbit_independent_checks.lean)
does more than restate the exported declarations.

First, it reverses the factor-three argument and proves for arbitrary
exponents, not only for indices already inside the first period,

\[
 \operatorname{residualClass}(e,n)
 =\operatorname{residualClass}(e,m)
 \iff n\equiv m\pmod{3^e}.                         \tag{3}
\]

The reverse direction lifts equality to the powers of ten modulo
\(3^{e+2}\); the forward direction cancels the exact integer factor three.
Equation (3) independently rules out a hidden shorter residual period and
proves that **any** \(3^e\) consecutive exponents form a complete period.

Second, the harness parametrizes the full residue-one coset as

\[
 \{x\in\mathbb Z/3^{e+1}\mathbb Z:x\equiv1\pmod3\}
 =\{1+3j:0\le j<3^e\}.                             \tag{4}
\]

It then combines (4) with T73's injectivity, cardinality, and reduction
theorems to prove exact equality between the residual period range and this
entire coset.  Thus the report's “one period runs bijectively through the
coset” conclusion is sound.  T73 itself exports the count and containment as
two separate declarations; the explicit set equality lives only in the
independent audit harness and is not promoted as a new centrally registered
research theorem.

The harness also checks the nontrivial small orbit

\[
   \operatorname{residualClass}(1,0),
   \operatorname{residualClass}(1,1),
   \operatorname{residualClass}(1,2)=4,7,1\pmod9.  \tag{5}
\]

It compiled with `--trust=0`.  Each of its four named independent theorems
reported a subset of the same allowlist, with no `sorryAx`.

## 4. Transfer to the three-primary report—and the exact stopping point

Let the report's primary exponent be \(E\ge2\).  T73 uses
\(e=E-2\).  The parameter translation is therefore exact:

| report claim | T73 object/result | verdict |
|---|---|---|
| \(g_n=(10^n-16)/3\), report (19) | `residualTen n` | exact |
| \(v_3(10^n-16)=1\), report (20) | `three_mul_residualTen` plus `residualTen_mod_three` | exact arithmetic content; no formal `padicVal` spelling |
| \(\operatorname{ord}_{3^E}(10)=3^{E-2}\), report (24) | `orderOf_tenUnit (E-2)` | exact |
| collision criterion, report (25) | unit criterion in T73; residual criterion independently derived in (3) | exact |
| complete coset, report (26) | range count plus reduction in T73; exact equality independently derived in (4) | exact |
| epoch formula for \(E_M,u_M\), report (6) | no depth \(M\), BBP coefficient, or partial sum occurs in T73 | outside formal scope |
| \(\delta_{M,n}=\beta_Mg_n\), report (21)--(22) | no \(\beta_M\) or multiplication-by-unit theorem occurs in T73 | outside formal scope |
| row-length and even/odd epoch coverage, report (27)--(32) | no \(L_M,U_M,\gamma_e\), or row window occurs in T73 | outside formal scope |
| full phase with \(\chi_{M,n}\), report (33) | no complementary CRT coordinate occurs in T73 | outside formal scope |

Multiplication by a fixed \(3\)-adic unit \(\beta_M\) would indeed permute
the coset, but T73 neither defines the BBP-derived unit nor proves that its
hypotheses hold.  Likewise, a complete isolated coset says nothing about the
synchronized complementary phase.  Any description of T73 as a formal proof
of the report's all-depth epoch theorem, proportional-row theorem, or a BBP
return would overstate its scope.

The file is imported directly by the central axiom audit.  It is not
currently imported by the optional top-level `TheoryLib.lean` barrel.  This
does not bypass the verifier—the audit import compiled it and the full gate
passed—but a consumer importing only `TheoryLib` will not receive T73.  That
is a nonblocking discoverability/integration note, not a trust gap under the
requested module-and-audit check.

## 5. Forbidden constructs, registration, and axiom surface

After stripping nested comments and strings, the source audit found none of:

- `sorry`, `admit`, `sorryAx`, or `native_decide`;
- new `axiom`, `opaque`, `constant`, `unsafe`, or `extern` declarations;
- `Lean.ofReduceBool`, `Lean.trustCompiler`, `implemented_by`, or `run_tac`.

`AxiomAudit.lean` imports the exact T73 module once and contains exactly one
`#print axioms` command for each of the nine theorem declarations—no missing,
extra, or duplicate T73 registration.  Every T73 result printed

```text
[propext, Classical.choice, Quot.sound]
```

and no other axiom.  The independent harness printed only subsets of that
same list.  The unchanged PowerShell gate independently parsed all audit
output against the exact three-name allowlist and passed.

## 6. Python replay and hygiene checker

The companion
[hygiene checker](t73_three_primary_orbit_independent_hygiene_check.py)
pins the inputs, compares declaration and registration name sets, scans the
code surface, and performs a finite arithmetic replay.  For
\(0\le e\le8\), it verifies the order certificate, enumerates every point in
one residual period, checks exact equality with the residue-one coset, and
checks two further period shifts.  Its retained output is:

```json
{
  "asserts_bbp_epoch_formula": false,
  "asserts_joint_crt_control": false,
  "asserts_pi_normal": false,
  "asserts_v1": false,
  "axiom_audit_registrations": 9,
  "claim_status": "experiment",
  "complete_coset_checks": 9,
  "forbidden_construct_hits": 0,
  "order_checks": 9,
  "period_shift_checks": 19682,
  "residual_orbit_points_checked": 9841,
  "status": "PASS",
  "t73_definitions": 3,
  "t73_theorem_declarations": 9
}
```

This finite replay has status `experiment`; it is not the proof.  The Lean
kernel checks and central axiom audit are the trust-bearing evidence.

## 7. Reproduction

From the repository root:

```bash
env LEAN_NUM_THREADS=4 lake build \
  TheoryLib.PiQuantitativeBlockHitting.T73T73ThreePrimaryOrbit
env LEAN_NUM_THREADS=4 lake env lean --trust=0 \
  TheoryLib/PiQuantitativeBlockHitting/T73T73ThreePrimaryOrbit.lean
env LEAN_NUM_THREADS=4 lake env lean --trust=0 \
  work/ultrapi-resume/t73_three_primary_orbit_independent_checks.lean
env LEAN_NUM_THREADS=4 lake env lean --trust=0 audit/AxiomAudit.lean
.venv/bin/python -m py_compile \
  work/ultrapi-resume/t73_three_primary_orbit_independent_hygiene_check.py
.venv/bin/python \
  work/ultrapi-resume/t73_three_primary_orbit_independent_hygiene_check.py
pwsh -NoProfile -File scripts/check.ps1
```

The focused module build completed all 8,480 dependency jobs.  Direct T73,
independent harness, and central audit compilation all exited successfully;
the final repository gate passed as quoted above.  Pre-existing style-linter
warnings in imported older modules were nonfatal and unrelated to T73.

## 8. Coordination record

This branch registered descendant-area watch
`watch:local:pi-digits:t73-three-primary-independent-audit-20260813` on
`local:pi-digits` for agent `codex-t73-independent-auditor`.  The initial poll
was empty at cursor and delivered sequence 57,287.  Observation events are
coordination signals only and were not used as mathematical evidence.  The
final poll was also empty at cursor and delivered sequence 57,287, so no
event was acknowledged.

## Final assessment

The frozen T73 module is a sound `machine-checked` generic arithmetic
component for the report's isolated three-primary orbit.  The independent
converse and coset derivations close the most plausible off-by-one and
“distinct subset versus full coset” gaps.  The sharp remaining boundary is
not local arithmetic: neither the BBP epoch theorem nor synchronized control
of the complementary CRT coordinates is present in T73.  Consequently this
formal progress is real but does not prove V1.
