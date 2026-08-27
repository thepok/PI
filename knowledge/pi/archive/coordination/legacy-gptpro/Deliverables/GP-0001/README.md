# GP-0001 — Salikhov to `PowerTenDiophantine`

Completed: 2026-08-21 UTC  
Agent: `pro-20260821T201629Z-gpt56pro-065a`

Claim labels:

- Salikhov source statement: `literature-checked` within the pinned T9 corpus.
- Source-to-T17 derivation below: `proof sketch`.
- C1: `conjecture`; unchanged.

## Verdict

Let `Q₀` be a denominator threshold supplied by Salikhov after choosing the
strictly admissible exponent `ν = 8`. Then every natural `A` satisfying

```text
1 ≤ A  and  Q₀ ≤ 10^A
```

has the following consequence:

```text
PowerTenDiophantine Real.pi 8 A.
```

Thus the pinned source supports the exact external statement

```text
∃ A : ℕ, 1 ≤ A ∧ PowerTenDiophantine Real.pi 8 A.
```

The smallest source-relative threshold is

```text
A* = min { a : ℕ | 1 ≤ a ∧ Q₀ ≤ 10^a }.
```

A simpler nonminimal witness is `A = Q₀ + 1`. The pinned theorem statement
and T9 extraction do not give a numerical value or upper bound for `Q₀`, so
no numeral for `A` is source-honest from those materials alone. This is an
information limit of the quoted statement, not a claim that Salikhov's proof
could never be effectivized by a separate constant audit.

`mu = 8` is the smallest natural exponent justified by the recorded bound.
A smaller natural exponent, in particular `mu = 7`, would assert a stronger
lower bound and does not follow from the source.

## Exact source convention

T9 records Salikhov's Theorem 1 in the form

```text
for all natural p,q with q ≥ q₀,
|pi - p/q| ≥ q^(-ν),
```

with exponent `ν = 7.6063...`; the final calculation is recorded as proving
the estimate for every `ν > 7.60630852...`. This report does not claim the
rounded endpoint. It fixes the unambiguous integer choice `ν = 8` and denotes
the corresponding threshold by `Q₀`.

The load-bearing source evidence is pinned in:

- `knowledge/pi/workstreams/pi-quantitative-block-hitting/library/t9/T9_DETERMINISTIC_ORBIT_AUDIT.md`;
- `knowledge/pi/workstreams/pi-quantitative-block-hitting/library/t9/retrieval_manifest.json`;
- `knowledge/pi/workstreams/pi-quantitative-block-hitting/library/t9/HASHES.sha256`.

The manifest identifies V. Kh. Salikhov, *On the irrationality measure of
pi*, Russian Mathematical Surveys 63 (2008), 570–572, DOI
`10.1070/RM2008v063n03ABEH004543`, and records exact theorem/page locators and
hashes for the retained PDF and text extraction.

## Denominator and exponent conversion

Fix `t : ℕ` with `A ≤ t`, and put `q = 10^t`. Monotonicity gives

```text
Q₀ ≤ 10^A ≤ 10^t = q.
```

For a positive integer numerator `p`, Salikhov therefore gives

```text
|pi - p/10^t| ≥ (10^t)^(-8)
                = 1 / (10^t)^8
                = 1 / 10^(8*t).
```

The last identity is the ordinary power law
`(10^t)^8 = 10^(t*8) = 10^(8*t)`. This is exactly T17's right-hand scale for
`mu = 8`, since its definition uses `10^(mu*t)`.

No reduced-fraction or nearest-integer premise is introduced: the exact
source statement recorded by T9 quantifies over all natural numerators and
denominators above the denominator threshold.

## Signed numerators and edge cases

T17 quantifies over `p : ℤ`, whereas the recorded source uses natural
numerators.

- If `p > 0`, cast it to a positive natural and apply Salikhov as above.
- If `p ≤ 0`, then `p/10^t ≤ 0`. Because `t ≥ A ≥ 1`,
  `1/10^(8*t) ≤ 1`, while

  ```text
  |pi - p/10^t| = pi - p/10^t ≥ pi > 3 > 1.
  ```

  Hence all zero and negative numerators satisfy the required inequality
  without using the literature theorem.
- Small positive numerators require no separate treatment because the source
  quantifies over every natural `p`; only the denominator is thresholded.
- For `t < A`, `PowerTenDiophantine` deliberately makes no assertion.

The condition `1 ≤ A` is necessary, not cosmetic. At `t = 0` and `p = 3`,
T17's left side is `1`, but

```text
|pi - 3| = pi - 3 < 1
```

because `3 < pi < 4`. Consequently
`PowerTenDiophantine Real.pi 8 0` is false. One cannot absorb the source's
finite exceptional range by setting `A = 0`.

## Consequence for T17

The exact definition is in
`TheoryLib/PiQuantitativeBlockHitting/T17T17PowerTenDiophantineReduction.lean`:

```text
PowerTenDiophantine x mu A :=
  ∀ t, A ≤ t → ∀ p : ℤ,
    1 / 10^(mu*t) ≤ |x - p/10^t|.
```

Therefore Salikhov externally instantiates T17 with

```text
mu = 8,
r = (mu - 1)*D + 1 = 7*D + 1,
```

and with some nonnumerical `A ≥ 1`. The unknown value of `A` changes only the
finite lower cutoff: T17 already returns `k ≥ A` as well as `k ≥ K` for every
requested `K`. It does not obstruct the theorem's qualitative unboundedness
form.

This does **not** discharge the premise inside Lean. No formalization of
Salikhov's theorem is present, and no literature theorem was inserted as an
axiom. The strongest source-honest status is:

- externally: `∃ A, PowerTenDiophantine Real.pi 8 A` is
  `literature-checked` plus the elementary `proof sketch` above;
- kernel-internally: T17 remains conditional on its explicit
  `PowerTenDiophantine` argument.

## Rejected alternatives

| Alternative | Verdict |
|---|---|
| Use `mu = 7` | Rejected: it is a stronger approximation lower bound than Salikhov supplies. |
| Use the decimal endpoint `7.60630852` as exact | Rejected: T9 records a strict `ν > ...` convention, and T17 requires a natural exponent. |
| Report an arbitrary numerical `A` | Rejected: the pinned statement does not numerically bound `Q₀`. |
| Set `A = 0` | Refuted explicitly by `t = 0`, `p = 3`. |
| Restrict T17 to natural or nearest numerators | Rejected: unnecessary weakening; the signed cases are elementary. |
| Add Salikhov as a Lean axiom | Rejected by the repository trust policy. |
| Treat this arithmetic bridge as cancellation | Rejected: it excludes T17's boundary-word branch but supplies no Fourier upper bound. |

## Verification and reproduction

Completed checks:

1. Compared T9's exact theorem/exponent convention with the source metadata
   and locators in the pinned retrieval manifest.
2. Audited the substitution `q = 10^t`, all inequality directions, the power
   identity, signed integer numerators, the finite exceptional range, and the
   `t = 0` counterexample.
3. Compared the result quantifier-by-quantifier with the committed
   `PowerTenDiophantine` definition and T17's use of `A ≤ k`.
4. Confirmed that no `TheoryLib/` or `audit/` file was changed and no new axiom
   was introduced.

No fresh Lean build is claimed: this task changes no formal source, and the
available runtime has no `lean`, `lake`, or `pwsh` executable.

No successful run of the archived T9 `reproduce.sh verify` is claimed. A
static audit found that the script and manifest retain the old workstream
layout: `HASHES.sha256` names `sources/` and `searches/` paths although the
current canonical directory is flattened, and the script's relative `ROOT`
calculation no longer reaches the repository root. The mathematical bridge
above relies on the committed pinned T9 report and manifest; repairing that
archival replay drift is a separate bounded maintenance task.

## Limitations and next bottleneck

- The source threshold `Q₀`, hence a numerical `A`, remains uneffectivized.
- The primary PDF was not freshly byte-replayed or rendered in this runtime;
  the exact theorem wording and endpoint convention come from the committed,
  hash-pinned T9 extraction and manifest.
- The result is not `machine-checked` and proves neither C1 nor its negation.
- Even after the external `mu = 8` instantiation, the decisive mathematical
  gap is an upper bound strong enough to contradict T17's aggregated Fourier
  lower bound. Irrationality measure alone gives no such cancellation.

The natural canonical promotion path, after an independent source replay, is
`knowledge/pi/results/intermediate/` as a compact external-hypothesis bridge.
A later generic Lean lemma may formalize only the elementary implication from
a source-shaped rational-approximation hypothesis to
`PowerTenDiophantine`; Salikhov's theorem itself must remain an explicit
external hypothesis unless independently formalized.

## Changed paths

- `GPTPro/Deliverables/GP-0001/README.md`

No canonical mathematical source was changed.
