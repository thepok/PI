# Independent audit: T72 colored repunit returns

Audit date: **2026-08-13 UTC**

## Verdict and claim boundary

**PASS.**  The theorem
`Theory.PiDigits.T72ColoredRepunitReturn.canonicalV1_iff_coloredRepunitReturns`
has the intended all-period, all-residue-color, arbitrarily-late, and
arbitrarily-accurate quantifiers.  Its two implications handle leading-zero
words and the all-nine cylinder without identifying the real endpoints zero
and one.  The module compiles, all of its theorem declarations are registered
in the axiom audit, and every reported axiom is on the repository's exact
allowlist.

This verdict labels the displayed equivalence `machine-checked`.  It does not
assert either side of that equivalence for pi.  Canonical V1 remains a
`conjecture`; this audit makes no `candidate resolution` or `verified
resolution` claim.

## Frozen inputs

| input | SHA-256 |
|---|---|
| `problems/local/pi-digits.txt` | `2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825` |
| `TheoryLib/PiQuantitativeBlockHitting/T72T72ColoredRepunitReturn.lean` | `c5b59557d1d95a26c0c451d9cd8d62d073d3d7f918467e5b2b888233d2c83373` |
| `TheoryLib/PiDigits/T20BaseTenOrbitDensity.lean` | `202d6db7dfc2f19db81c3cb96b856d36969652e54099c43e0d51b6ab62913126` |
| `TheoryLib/PiDigits/T21PiDigitsV1V3Relationship.lean` | `aaacf99dd9b916e7fbca8ce1054d462975dd3b75c5358a920ed67d90c1c4bbb5` |
| `audit/AxiomAudit.lean` | `4d03ce870c5f225b5d69fb76150481b68002fbd59fd5413fc8e62602bc6c4a85` |
| `scripts/check.ps1` | `953387f14651d68915361ca5baf1514ed1d22a434e1d2b1d4d417df62d3271b3` |

The T72 source preserves the canonical local source path and its exact hash.
The formal files were read and tested but not altered by this audit.

## 1. Exact statement and quantifiers

T72 defines

```lean
def ColoredRepunitReturns (x : ℝ) : Prop :=
  ∀ P : ℕ, 0 < P → ∀ k : Fin (repunit P), ∀ N : ℕ, ∀ ε : ℝ,
    0 < ε → ∃ n : ℕ, N ≤ n ∧
      |T20.baseTenOrbit x n - repunitGridPoint P k| < ε
```

where

\[
q_P=10^P-1,
\qquad
\operatorname{repunitGridPoint}(P,k)=\frac{k}{q_P},
\qquad
0\le k<q_P.
\]

Thus the elaborated proposition has, in the required order:

1. every natural period `P` subject to `0 < P`;
2. every `k : Fin (10^P - 1)`, hence every residue representative
   \(0,\ldots,10^P-2\);
3. every late-start threshold `N`;
4. every real accuracy `ε` subject to `0 < ε`;
5. a witness `n` satisfying both `N ≤ n` and the strict approximation.

The period hypothesis makes the repunit positive before a color is used.
There is no hidden uniformity swap: `n` may depend on `P`, `k`, `N`, and
`ε`, exactly as the displayed recurrence condition requires.

The distance is ordinary real absolute value.  Consequently color zero can
only be approached near zero, not by wrapping around from points near one.
This is an important endpoint safeguard.

## 2. Decimal words imply all late colored returns

For a nonnegative real `x`, T20's `EveryFiniteDecimalWord x` supplies every
finite word in the floor-based decimal stream.  T21's registered equivalence
upgrades this to occurrence after every threshold `N`: an occurrence of
`List.replicate N 0 ++ w` puts the suffix `w` at an index at least `N`.

Fix `P > 0`, a color `k`, `N`, and `ε > 0`, and set

\[
y=\frac{k}{10^P-1}\in[0,1).
\]

The proof chooses `m` with \(10^{-m}<\varepsilon\), requests the first `m`
floor-based digits of `y` after `N`, and applies mathlib's digit-prefix
distance bound.  The two reconstituted numbers both lie in `[0,1)`, so the
matching prefix gives

\[
\left|\operatorname{fract}(10^n x)-y\right|
\le 10^{-m}<\varepsilon.
\]

This also covers `k = 0`: the requested prefix is a string of zeroes, and the
ordinary absolute-value bound forces a genuinely small orbit point rather
than accepting a point near one.  The T21 step retains the arbitrary `N`, so
the forward implication does not weaken "arbitrarily late" to a single
occurrence.

## 3. Colored returns imply every word, including boundary cylinders

Let `w` have length `m`, let `a = T20.wordValue w`, and put

\[
Q=10^m,
\qquad
P=m+1,
\qquad
q_P=10Q-1,
\qquad
k=10a+5.
\]

T20 proves \(0\le a<Q\).  Hence \(0\le 10a+5<10Q-1\), so this is a valid
`Fin q_P` color.  Direct cross-multiplication gives

\[
\frac aQ
< \frac{10a+5}{10Q-1}
< \frac{a+1}{Q}.
\]

The left numerator difference is \(5Q+a>0\); the right numerator difference
is \(5Q-a-1>0\), using \(a<Q\).  Therefore the chosen grid point is strictly
inside the real decimal cylinder for `w`.

This single construction audits both sensitive endpoints:

- For a leading-zero word with `a = 0`, the color is
  \(5/(10Q-1)>0\), strictly inside \([0,1/Q)\).
- For the all-nine word with `a = Q-1`, the color is
  \((10Q-5)/(10Q-1)<1\), strictly inside \([(Q-1)/Q,1)\).
- For the empty word, `Q = 1` and the color `5/9` lies inside `[0,1]`; the
  resulting digit obligation is correctly vacuous.

Taking `ε` to be the minimum of the two positive margins, a colored return
at threshold zero lies in the half-open word cylinder.  T20's cylinder lemma
then fixes every digit of `w`, and its orbit-shift lemma transports those
digits back to positions `n + i` in `x`.

There is a precise scope distinction worth retaining.  The formal color type
contains `0` but not the second split endpoint `q_P/q_P = 1`; it is the
ordinary residue-color set, not the `q_P + 1` split-color set of a literal
zero/nine endpoint encoding.  This is not a defect in the equivalence.  The
all-nine cylinder is recovered by the strict interior color above, while the
real-distance convention prevents color zero from silently standing for
one.  A downstream statement claiming that T72 quantifies over both split
endpoint colors would, however, be inaccurate.

## 4. Canonical specialization

The generic implications yield

```lean
T20.EveryFiniteDecimalWord x ↔ ColoredRepunitReturns x
```

for every nonnegative real `x`.  T72 then composes this with T20's
`v1_iff_pi_baseTenOrbitDense` and the generic orbit-density equivalence at
`x = Real.pi`.  The final declaration is exactly

```lean
Theory.PiDigits.V1 ↔ ColoredRepunitReturns Real.pi
```

and its proof term is an equivalence composition.  It contains no witness of
either proposition and therefore proves no decimal word occurrence for pi.

## 5. Registration and forbidden-construct audit

`audit/AxiomAudit.lean` imports the exact module and registers every theorem
declaration in it:

1. `repunit_pos`;
2. `repunitGridPoint_mem_Ico`;
3. `decimalPrefix_length`;
4. `abs_baseTenOrbit_sub_le_of_prefixMatch`;
5. `everyFiniteDecimalWord_implies_coloredRepunitReturns`;
6. `wordInteriorGridPoint_mem_wordCylinder`;
7. `coloredRepunitReturns_implies_everyFiniteDecimalWord`;
8. `everyFiniteDecimalWord_iff_coloredRepunitReturns`;
9. `baseTenOrbitDense_iff_coloredRepunitReturns`;
10. `canonicalV1_iff_coloredRepunitReturns`.

The remaining T72 declarations are definitions, not unregistered theorem
claims.  A targeted source scan found no `sorry`, `admit`, new `axiom`,
`opaque`, `unsafe`, `native_decide`, compiler-trusting hook, or external
implementation in T72.  `noncomputable section` is ordinary logical code and
is not a trust shortcut.

Direct compilation printed the same dependency list for all ten registered
theorems:

```text
[propext, Classical.choice, Quot.sound]
```

These are exactly the three axioms permitted by `scripts/check.ps1`; no other
axiom was reported.

## 6. Verification replay

The targeted module replay was:

```bash
lake env lean \
  TheoryLib/PiQuantitativeBlockHitting/T72T72ColoredRepunitReturn.lean
```

It exited successfully and printed the allowed dependency list above for all
ten theorems.

The repository gate was then run without modifying its configuration:

```bash
pwsh -NoProfile -File scripts/check.ps1
```

It completed all 8,493 build jobs and ended with:

```text
PASS: kernel build, exploit scan, and exact-allowlist axiom audit succeeded.
```

Pre-existing linter warnings were nonfatal and unrelated to T72.  No separate
checker was added: Lean kernel replay plus the repository's independent
exact-allowlist gate is materially stronger than a source-text checker for
this task.

## 7. Coordination record

This audit registered the descendant-area watch
`watch:ultrapi:t72-colored-repunit-independent-audit-20260813` on
`local:pi-digits` for agent `codex-ultrapi-t72-colored-audit`.  The initial
poll was empty at cursor 56,943.  Observation events, if any, are treated only
as coordination signals and never as mathematical evidence.  The final poll
was also empty at cursor and delivered sequence 56,943, so there was no event
to acknowledge.

## Final assessment

T72 is a sound `machine-checked` reformulation of canonical V1.  It correctly
formalizes every positive period, every ordinary repunit residue color, every
late threshold, and every positive accuracy.  Its real-distance and interior-
color choices close the leading-zero and all-nine boundary cases.  The exact
axiom registrations are complete and clean.  The module advances the trusted
reduction infrastructure only; canonical V1 itself remains a `conjecture`.
