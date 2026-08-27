# π decimal disjunctivity: active frontier

Status: `conjecture`
Last audited: 2026-08-27 UTC

No theorem in this repository proves V1, decimal density, or normality of π.
The proof authority is [`TheoryLib/`](TheoryLib/) and
[`audit/AxiomAudit.lean`](audit/AxiomAudit.lean).

## Exact target

[`Theory.PiDigits.V1`](TheoryLib/PiDigits/T7Statements.lean) is

```text
∀ s : List (Fin 10), ∃ n : ℕ,
  ∀ i < s.length, piDigit (n+i) = s[i].
```

Leading-zero words and overlaps are included. The empty word is vacuous.
The normalized source and ambiguity record is
[`TARGET.md`](knowledge/pi/active/TARGET.md).

## Shortest current verified consumer path

T148/T153/T156 convert a sufficient lower bound for the complete primitive
boundary Fourier sum into a hit of the prescribed decimal cylinder. T176–T179
decompose child transport while retaining the predecessor digit, suffix, and
target phase. T189 gives the exact fresh-block sector identity and the final
one-sided child-surplus consumer. T190 supplies a deterministic
complementary-rank alignment lemma when suitable π-specific rank bounds are
available.

The exact theorem names and claim boundaries are recorded in
[`VERIFIED_CONSUMER_PATH.md`](knowledge/pi/active/VERIFIED_CONSUMER_PATH.md).

## T189 natural-diagonal frontier

At a positive node `(q,A)` with old horizon `q` and new horizon `Q=10q`, let

```text
G_d = B(Q,A+dq,q) - B(q,A,q),
D_d = B(Q,A+dq,Q) - B(Q,A+dq,q)
    = q(Delta_0 + Xi_d) - 21/10.
```

Here `Xi_d` is T179's literal target-signed predecessor-digit/suffix
correlation over the fresh π block. Fresh-monotone regeneration is

```text
exists d<10: D_d > 0 and G_d + D_d > 0.             (FMR)
```

The minimal witness-preserving split is

```text
R1: S_+={d<10 : D_d>0} is nonempty;
R2: exists d in S_+ : G_d+D_d>0.
```

Separate existential witnesses are invalid. Assuming an unbounded family of
already reached positive nodes is circular unless the same argument constructs
that path. One coherent predecessor ray still covers only factors of its
selector word, so V1 later needs viable branching or word coverage.

Full definitions and quantifiers:
[`T189_FMR_R1_R2.md`](knowledge/pi/active/T189_FMR_R1_R2.md).

## First open π-specific lemma

The first unproved arithmetic rung is a non-tautological actual-π lower bound
for the literal paired predecessor sectors strong enough to make R1 hold. A
clean non-circular local formulation is:

```text
for every q=10^k and every positive node (q,A),
exists r in {1,...,5}:
  Delta_0(q,A) + |P_r(q,A)|/2 > 21/(10q),
```

or a weaker direct theorem implying `max_d Xi_d > 21/(10q)-Delta_0`.
Here `P_r=C_r+conj(C_(10-r))` uses the complete actual-π fresh block and
literal target phase. The deterministic inequality
`max_d Xi_d >= |P_r|/2` is sharp; the missing step is the π-specific lower
bound, not that inequality. This uniform version is stronger than logically
necessary; a weaker version is admissible only if it jointly constructs the
recursive selector/path rather than quantifying over nodes assumed to have
been reached. R2 then still needs same-digit alignment.

The preferred aligned alternative clips the inherited deficit
`h_d=(-G_d)_+`, sets `Y_d=D_d-h_d`, and applies the sharp regular-decagon
envelope to its mean and first DFT sector. It yields the sufficient premise

```text
q*Delta_0-21/10-hbar
  + gamma_10(hhat_1-(q/2)*P_1) > 0.                (DC1)
```

This corrected audited `proof sketch` preserves the same FMR witness and uses
only one fresh paired sector, but supplies no actual-π lower bound. It is the
preferred target when an arithmetic source couples past deficits to the fresh
sector; Pair-π remains the simpler R1-only fallback.

This is a research target, not a proved theorem. See
[`FIRST_OPEN_PI_LEMMA.md`](knowledge/pi/active/FIRST_OPEN_PI_LEMMA.md).

## What is known and what is excluded

- A certified finite π seed and two replay levels show the consumer is
  non-vacuous, but finite data cannot provide unbounded transport.
- T190 is machine-checked, but no useful complementary actual-π rank premise
  is known on an unbounded reached path.
- Paired-sector amplitudes alone do not imply R2; exact finite vectors separate
  amplitude information from same-digit alignment.
- The paired sector is a formally nonzero Laurent polynomial evaluated at
  `exp(2π²i)`, but current transcendence theory gives neither evaluated
  nonvanishing nor the required quantitative lower bound.
- BBP, Machin, p-adic, rational-shadow, generic lacunary, topological, scalar
  energy, and low-dimensional empirical routes remain admissible only when a
  new ingredient directly controls the literal target-signed rung.

The ten live warnings are indexed in
[`SEPARATORS.md`](knowledge/pi/active/SEPARATORS.md). Broader history is archived
and should not be loaded during ordinary research.

## Operator rule

Creative work attacks the first open rung or a strictly shorter route to the
same consumer. Empirics falsify concrete lemmas; Lean formalizes surviving
ones. Keep the active core small and archive superseded notes immediately.
