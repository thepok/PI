# T63 exact five-adic transient audit

Audit date: **2026-08-12 UTC**

Target: [`problems/local/pi-digits.txt`](../../problems/local/pi-digits.txt)

Target SHA-256:
`2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825`

Provenance: the immutable local question has no external source URL; none is
invented.  This report follows [`problems/TEMPLATE.md`](../../problems/TEMPLATE.md)
inside the existing problem record.

## Outcome and exact claim status

The elementary five-adic transient claimed in
[`hutton_global_crt_attack.md`](hutton_global_crt_attack.md) is now
`machine-checked`.  For every `K e : ℕ`, if

\[
 5^e\le 4K+3<5^{e+1},
\]

then Lean proves both

\[
 v_5(H_K)=-e,
 \qquad
 v_5(\operatorname{den}(H_K))=e,
 \quad H_K=\texttt{huttonLowerRat K}.
\]

The theorem includes `K=0`: there `4K+3=3`, `e=0`, and the reduced
denominator has five-adic order zero.  The inequalities are the exact
integer characterization of `e=floor(log_5(4K+3))`; no real logarithm and
no rounding convention enter the formal statement.

This is a `machine-checked` denominator result, not a proof of the canonical
every-word statement V1.  It gives the exact exponent of five in the
base-10 transient component.  It does **not** by itself give the full decimal
preperiod length (which can also depend on the denominator's two-adic
exponent), and it supplies no control of the complementary numerator phase,
no decimal-cylinder hit, and no distribution theorem for pi.

## Normalized statement and quantifiers

The formal theorem has the following quantifier order:

```text
∀ K e : ℕ,
  5^e ≤ 4*K+3 → 4*K+3 < 5^(e+1) →
  padicValRat 5 (huttonLowerRat K) = -(e : ℤ)
```

and the denominator corollary has the same hypotheses and concludes

```text
padicValNat 5 (huttonLowerRat K).den = e.
```

Ambiguities resolved:

- `den` is Lean's positive reduced rational denominator, not an unreduced
  common denominator of the Taylor sum.
- `v_5(0)` is irrelevant: T63 separately proves
  `0 < huttonLowerRat K` for every `K`.
- Both possible minimum exponents are treated.  The term at `3*5^e` is
  included exactly when `3*5^e ≤ 4*K+3`.
- The endpoint inequalities are closed below and open above.  This makes
  `e` unique and handles exact powers of five correctly.

## Machine-checked proof architecture

Write the paired term at odd exponent `r=2k+1` as

\[
 U_k=
 \frac{4(-1)^k(2\cdot7^r+3^r)}{r3^r7^r}.
\]

T63 checks the following chain rather than treating the residue computation
as an informal side condition.

1. For odd `r`, reduction in `ZMod 5` gives
   `2*7^r+3^r = 2^r`, hence the cancellation factor is a five-unit and
   `v_5(U_k)=-v_5(r)`.
2. If `r≤4K+3<5^(e+1)` is odd and `v_5(r)=e`, divisibility by `5^e`
   and the quotient bound `<5` force `r=5^e` or `r=3*5^e`.
3. The index of `5^e` is even and the index of `3*5^e` is odd.  In the
   one-term case the minimum is therefore unique.
4. In the two-term case, multiplication by `5^e` and passage to one common
   denominator gives an explicit integer numerator.  Lean proves that this
   numerator is `2` in `ZMod 5`; the common denominator is also a five-unit.
   Equivalently, the separately normalized pair residues are `3` and `1`,
   whose sum is nonzero modulo five.
5. Every remaining paired term has valuation at least `1-e`.  The finite
   ultrametric sum lemma retains that lower bound for the regular remainder.
   Adding it to the nonzero minimum layer preserves valuation `-e`.
6. A reduced-rational lemma converts valuation `-e` to exact denominator
   multiplicity `e`.  Its proof explicitly handles `e=0`: reducedness rules
   out simultaneous positive numerator and denominator valuations.

The proof introduces no axiom, `sorry`, `admit`, `native_decide`, unsafe
declaration, or opaque proof constant.

## Artifacts and verification

Formal module:
[`T63T63HuttonFiveAdicTransient.lean`](../../TheoryLib/PiQuantitativeBlockHitting/T63T63HuttonFiveAdicTransient.lean)

Point-in-time SHA-256:

```text
d7f42ff02ae0ab0877f8f165e88c9353e8bf72ee49f00c71087198f9cd41aaa2  TheoryLib/PiQuantitativeBlockHitting/T63T63HuttonFiveAdicTransient.lean
```

The module is imported by `TheoryLib.lean`.  Every one of its **33** named
declarations has a local `#print axioms` line and a matching registration in
[`audit/AxiomAudit.lean`](../../audit/AxiomAudit.lean).  The counts were
checked mechanically as `33 / 33 / 33`.

Focused verification completed successfully:

```text
lake build TheoryLib.PiQuantitativeBlockHitting.T63T63HuttonFiveAdicTransient
lake env lean audit/AxiomAudit.lean
```

The direct audit reports only the repository allowlist
`propext`, `Classical.choice`, and `Quot.sound`.  A forbidden-token scan of
the module was clean.  The full repository gate was then run as
`pwsh -File scripts/check.ps1` and ended with
`PASS: kernel build, exploit scan, and exact-allowlist axiom audit succeeded.`
The exact-arithmetic companion replay
[`hutton_global_crt_check.py`](hutton_global_crt_check.py) also reran and
reported `all exact checks passed`; this replay remains an `experiment`,
whereas the T63 theorem itself is `machine-checked`.

## Scope and next obstruction

T63 validates the identity

\[
 b_K=v_5(\operatorname{den}(H_K))
     =\lfloor\log_5(4K+3)\rfloor
\]

used in the global CRT attack.  It does not validate the rest of that
attack automatically.  After removing this known transient, the unresolved
task is still to control the actual reduced numerator simultaneously in the
growing selected-prime factor and its correlated complementary denominator.
That phase problem, not the five-adic valuation, is the remaining barrier to
a decimal-cylinder theorem.

## Independent review

- Statement and proof construction: machine checked by Lean on 2026-08-12.
- Axiom registration: direct audit passed on 2026-08-12.
- Independent human/domain review: not yet recorded.
- Novelty/attribution review: not claimed; this is an elementary formal
  support theorem within the ongoing V1 investigation.
