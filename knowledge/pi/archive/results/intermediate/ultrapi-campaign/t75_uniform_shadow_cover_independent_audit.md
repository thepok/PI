# Independent audit: T75 uniform shadow cover

Audit date: **2026-08-13 UTC**

Canonical target: [problems/local/pi-digits.txt](../../problems/local/pi-digits.txt),
SHA-256
`2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825`.
This is the preserved local source; no external source URL is invented.

## Conclusion and claim boundary

The abstract T75 implication is `machine-checked`.  Its quantifiers, shift
sign, arbitrarily-late conclusion, circle metric, ordinary real metric, and
the endpoint color zero all survive an independent Lean rederivation.  The
four T75 theorems are imported by the barrel, registered in the central
axiom audit, compile with `--trust=0`, and use exactly the allowed axioms
`propext`, `Classical.choice`, and `Quot.sound`.  The full repository gate
passes all 8,493 jobs.

No BBP shadow family is proved to satisfy T75's premises.  In particular,
uniform endpoint-grid coverage is still a `conjecture`, and this audit does
not prove canonical V1 for pi.  The correct status is therefore:

- T75's conditional abstract implication: `machine-checked`;
- the required BBP uniform-cover premise: `conjecture`;
- every finite decimal word occurring in pi: still `conjecture`.

This is not a `candidate resolution` or a `verified resolution`.

## 1. Frozen objects

| object | SHA-256 |
|---|---|
| canonical local source | `2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825` |
| T72 colored-return interface | `c5b59557d1d95a26c0c451d9cd8d62d073d3d7f918467e5b2b888233d2c83373` |
| audited T75 module | `002cac6a91c36f1e23499c16c0fafd1c259d5d93b974697ffc512ca4d6e4cc9b` |
| independent Lean replay | `c144ad045d93f433256ba3264a2d18be4af145ddc4c4f6969bd5b7bca18e24ee` |
| independent checker | `3534523d5966d74eff1f64fa9bffecfbe38b026d16a6cc90a82f0ea43da010c9` |
| barrel at audit time | `ce5948ca9e83608aac03cb62ad10ccb04bf064022ca28978dccf3b42d36a897e` |
| central axiom audit at audit time | `9bafe79851f4b8f8d3c892985dcb74e8180b33193a494bdf43fd5f5285faed93` |

The independent Lean file imports T75 for its public definitions but invokes
none of T75's four bridge theorems.  It reconstructs each logical step from
the definitions and the earlier T26/T72 interfaces.

## 2. Quantifier audit

For arbitrary `x`, fixed circle shift `s`, row widths `w(e)`, shadows
`z(e,j)`, and attached natural exponents `n(e,j)`, T75 assumes:

1. for every real radius (r>0), some threshold (E_c) makes **every** row
   (e\ge E_c) cover **every** circle target (y) within (r);
2. for every natural threshold (N), some (E_n) makes **every** exponent
   in **every** row (e\ge E_n) satisfy (N\le n(e,j));
3. for every (r>0), some (E_e) makes **every** shadow in **every** row
   (e\ge E_e) lie within (r) of
   \(\{10^{n(e,j)}x\}-s\) on the circle.

Given a target `(y,N,epsilon)`, the proof chooses one common row

\[
 e=\max(E_c,E_e,E_n).
\]

Coverage supplies its index `j`; the universal quantifiers in the other two
premises apply to that same `j`.  Thus the proof cannot silently select a
well-covering point whose exponent is early or whose shadow error is
uncontrolled.  If a row had width zero, the coverage premise itself could
not supply `j`; no empty-row loophole is used.

The conclusion retains both arbitrary target and arbitrary starting time:

\[
 \forall y\ \forall N\ \forall\varepsilon>0\ \exists n\ge N:
 d_{\mathbb R/\mathbb Z}(\{10^n x\},y)<\varepsilon.
\]

An estimate available only on even endpoints or another cofinal subsequence
must be presented by reindexing those rows.  T75 itself requires every
sufficiently late row of the supplied family; it does not infer cofinality.

## 3. Shift-sign and triangle audit

The error premise says

\[
 z(e,j)\approx \{10^{n(e,j)}x\}-s.
\]

To approximate a requested target (y), coverage is correctly requested at
(y-s), not (y+s).  Translation invariance then gives

\[
 z(e,j)+s\approx y,
 \qquad z(e,j)+s\approx\{10^{n(e,j)}x\}.
\]

T75 uses radius (\varepsilon/3), so the triangle bound is
(2\varepsilon/3<\varepsilon).  The independent replay uses
(\varepsilon/4), obtaining the same conclusion with a different slack.
This confirms that the result is not an artifact of an exact constant.

## 4. Circle distance versus ordinary real distance

T72's `ColoredRepunitReturns` requires

\[
 \left|\{10^n x\}-\frac{k}{10^P-1}\right|<\varepsilon
\]

as ordinary real distance, for every (P>0), every
(0\le k<10^P-1), every threshold (N), and every (\varepsilon>0).
Circle proximity alone is insufficient at the endpoints, so the two cases
must be separated.

### Positive colors

For (y=k/(10^P-1)>0), T72 gives (0<y<1).  T75 chooses

\[
 r=\min\!\left(\frac\varepsilon2,\frac y2,
                  \frac{1-y}{2}\right).
\]

Hence (r<y) and (r<1-y).  T26's endpoint-safe circle lemma then rules out
all translated representatives and turns circle distance below (r) into
ordinary absolute distance below (r<\varepsilon).

### Color zero

For (y=0), aiming at zero on the circle would wrongly permit orbit points
near one.  T75 instead chooses the positive interior center

\[
 c=\min(\varepsilon/4,1/4),\qquad r=c/2.
\]

Because (r<c) and (r<1-c), T26 converts the circle hit at (c) to

\[
 |\{10^n x\}-c|<c/2.
\]

The fractional part is nonnegative, so

\[
 0\le\{10^n x\}<3c/2\le3\varepsilon/8<\varepsilon.
\]

The independent replay repeats this argument with
(c=\min(\varepsilon/8,1/8)), again proving an ordinary real return to zero.
Thus wraparound near one cannot witness color zero in either derivation.

Finally, the proof establishes **all** repunit colors before invoking T72's
equivalence.  It does not make the invalid inference that a single return to
zero implies V1.

## 5. Independent Lean replay

[t75_uniform_shadow_cover_independent_replay.lean](t75_uniform_shadow_cover_independent_replay.lean)
contains five separately named theorems:

1. independent cover/error/late-exponent transfer to circle density;
2. independent endpoint-zero return;
3. independent positive-interior return;
4. independent assembly of all T72 repunit colors;
5. independent conditional implication to canonical V1 for pi.

Compiled with:

```text
lake env lean --trust=0 \
  work/ultrapi-resume/t75_uniform_shadow_cover_independent_replay.lean
```

All five declarations depend on exactly:

```text
[propext, Classical.choice, Quot.sound]
```

## 6. Registration, forbidden constructs, and repository gate

The T75 import occurs once in `TheoryLib.lean` and once in
`audit/AxiomAudit.lean`.  All four public T75 theorems have explicit
`#print axioms` entries in the central audit.  Focused scans found no `sorry`,
`admit`, `native_decide`, axiom declaration, opaque declaration, or unsafe
proof declaration in T75 or the independent replay.

The following checks passed:

```text
lake env lean --trust=0 \
  TheoryLib/PiQuantitativeBlockHitting/T75T75UniformShadowCover.lean
lake env lean --trust=0 TheoryLib.lean
lake env lean --trust=0 audit/AxiomAudit.lean
.venv/bin/python \
  work/ultrapi-resume/t75_uniform_shadow_cover_independent_check.py
pwsh -NoProfile -File scripts/check.ps1
```

The final gate reported:

```text
Build completed successfully (8493 jobs).
PASS: kernel build, exploit scan, and exact-allowlist axiom audit succeeded.
```

## 7. What remains open

T75 cleanly identifies, but does not solve, the analytic bottleneck.  A BBP
application must still construct a concrete cofinal family and prove all
three premises, most importantly uniform circle coverage at every positive
scale.  Finite largest-gap measurements remain `experiment`; their proposed
asymptotic decay remains a `conjecture`.  The shadow-error and late-exponent
conditions also have to be instantiated for the exact chosen indexing.

Accordingly, T75 is a sound endpoint-safe conditional bridge, not an
unconditional proof about pi's digits.
