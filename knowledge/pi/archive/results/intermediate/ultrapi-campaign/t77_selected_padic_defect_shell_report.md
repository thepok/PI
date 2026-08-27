# T77 selected three-adic defect shell: formal scope and remaining bridge

Audit date: **2026-08-13 UTC**

Canonical target: [problems/local/pi-digits.txt](../../problems/local/pi-digits.txt),
SHA-256
`2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825`.
This is Marcel's immutable local question and has no external source URL; none
is invented here.

Inputs checked before formalization:

| artifact | SHA-256 |
|---|---|
| [primary selected-path report](bbp_selected_padic_path_20260813.md) | `5d8a4259ec2ad4f0f0d77558ce854ac345a79b10b672060419cc6445e67481` |
| [independent selected-path audit](bbp_selected_padic_path_20260813_independent_audit.md) | `17248399e0aed68a1392b904be1afa047dca5dc9c8fd88a04d94bbc592e22e7a` |

## Outcome and claim boundary

The new file
[T77T77SelectedPadicDefectShell.lean](../../TheoryLib/PiQuantitativeBlockHitting/T77T77SelectedPadicDefectShell.lean)
has label `machine-checked` for the exact claims listed below.  It contains no
`sorry`, `admit`, new axiom, `native_decide`, unsafe declaration, or opaque
proof shortcut.  Its declarations use only the allowlisted logical axioms
reported by the repository gate.

The all-depth rational congruence

\[
 9B_{M_{e+2}}-B_{M_e}\equiv1\pmod {9\mathbb Z_{(3)}}
\]

retains label `proof sketch`.  T77 does **not** assert it.  In particular, the
machine-checked residue ledger is not silently identified with the rational
shell: the missing localization bridge is stated explicitly below.

Canonical V1 remains a `conjecture`.  T77 proves no selected-correlation
decay, deterministic exceptional-fibre escape, decimal-word occurrence,
`candidate resolution`, or `verified resolution`.

## Machine-checked content

Let the four BBP poles be the exact rational functions already defined in
T74, let `bbpPartial M` be their inclusive sum through `M`, and define

\[
   \operatorname{endpointDefect}(M)=9B_{9M+13}-B_M.
\]

T77 proves:

1. `sum_range_nine_blocks_five_tail`: a range of length `9R+5` is exactly
   `R` complete nine-blocks followed by residues `0,...,4`.
2. `poleOne_defect_eq_shell` through `poleFour_defect_eq_shell`: each exact
   rational pole defect equals its explicit paired-error, complete-complement,
   final-tail, and (where required) boundary decomposition.
3. `endpointDefect_eq_shell`: the full rational endpoint defect equals the sum
   of those four exact shells for every natural `M`.  This machine-checks all
   inclusive cutoffs and the two compensating boundary signs in the primary
   argument.
4. `selectedDepth_mod_nine_of_twice`: for every `t>=1`, the intended even
   epoch depth

   \[
       M_{2t}=\frac{5\,3^{2t}-13}{8}
   \]

   is `4 mod 9`.  The proof first checks `9^t = 9 mod 72`.
5. `pairCountResidue_of_endpoint`: if `M=4 mod 9`, the four inclusive pair
   counts reduce to `(0,0,2,2) mod 3`.
6. `heightOneNonselected_completeBlock_table`: enumeration from the actual
   four slopes, intercepts, selected lifts, and coefficient classes gives zero
   for every complete nonselected residue block.
7. `nonselectedTailResidue_table` and `regularBoundaryResidue_table`: the
   actual final-block and boundary computations are `(6,3,6,0)` and
   `(2,5,0,0)` modulo nine.
8. `pairedResidue_table`, `poleShellResidue_table`, and
   `poleShellResidue_sum`: the paired column is `(0,0,3,3)`, the pole totals
   are `(8,8,0,3)`, and their total is one in `ZMod 9`.

All 26 supporting theorem declarations are imported by `TheoryLib.lean` and
registered individually in `audit/AxiomAudit.lean`.

## Exact missing lemmas for full SP1

The independent audit confirms the paper derivation, but the following chain
has not yet been formalized and is not implied by the finite `ZMod 9` ledger.

1. Define and develop a usable exact congruence interface for
   `\mathbb Z_(3)` inside rational numbers, for example in terms of
   `padicValRat 3`, including addition, finite sums, division by a three-adic
   unit, and reduction modulo `3` and `9`.
2. For every positive `t`, formalize

   \[
     Q_t=\frac{16^t-1}{15t}\in\mathbb Z_{(3)},\qquad Q_t\equiv1\pmod3.
   \]

   The intended proof expands `Q_t` binomially and needs the uniform bound

   \[
   v_3\!\left(\frac{\binom ts}{t}15^{s-1}\right)
      \ge s-1-v_3(s)\ge1\quad(s\ge2).
   \]

   Mathlib has generic `padicValRat` arithmetic, but no directly matching
   declaration for this cancelled binomial quotient.
3. Apply that lemma after writing each pole denominator as `3^j u` to prove,
   uniformly in `r`, that the exact paired error lies in `3 Z_(3)` and that
   its quotient by three has residue `c_i m_i mod 3`.
4. Prove the rational-to-residue classification for every nonselected term:
   height zero vanishes after multiplication by nine; height one reduces to
   `3 c_i u^-1`; and no larger height occurs outside the selected residue.
5. Lift the machine-checked complete-block, tail, and boundary enumeration
   through that interface, then combine it with `endpointDefect_eq_shell`.

Only after these steps would a Lean theorem stating SP1 be honest.  Even SP1
would not complete canonical V1: it controls the universal defect increment,
while the selected path still contains the unresolved hidden carry.

## Verification

The focused Lean compilation passed.  The final `scripts/check.ps1` run also
reported:

```text
Build completed successfully (8493 jobs).
PASS: kernel build, exploit scan, and exact-allowlist axiom audit succeeded.
```

The audit output for every T77 declaration contains only the repository's
allowlisted `propext`, `Classical.choice`, and/or `Quot.sound` (with some
arithmetic declarations using fewer).

## Coordination

This branch registered descendant-area watch
`ultrapi-padic-formal-20260813` on `local:pi-digits` for agent
`codex-ultrapi-padic-formal`.  Its initial poll was empty at cursor and
delivered sequence 57,502, so no event was acknowledged.  Observation events
were treated only as coordination signals and supplied no mathematical
evidence.
