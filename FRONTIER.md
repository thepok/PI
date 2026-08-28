# π decimal disjunctivity: active frontier

Status: `conjecture`
Last audited: 2026-08-28 UTC

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

Uniform Pair-π and uniform local Aligned-π positivity are false.  A
directed-interval `experiment`, independently reproduced in two interval
engines, gives an actual positive node `(q,A)=(1000,689)` where all five Pair
margins are negative and the DC1 right side is about `-7199.927`, yet literal
FMR holds strongly and uniquely at `d=8`.  This does not refute FMR, DC1 as a
deterministic inequality, or pathwise uses of either statistic.  It shows that
the favorable child can require coherent interference of several character
sectors.

The first honest arithmetic rung is therefore a non-tautological actual-π
theorem for the complete same-child correlation, or a genuinely smaller
multi-sector statistic that preserves its relative phases.  It must jointly
construct an unbounded selector/path

```text
q_(k+1)=10*q_k,       A_(k+1)=A_k+d_k*q_k,
D_(k,d_k)>0,          G_(k,d_k)+D_(k,d_k)>0.
```

Quantifying over already reached nodes is circular. Reconstructing all ten
coordinates is merely FMR in Fourier notation.  A smaller statistic counts
only when a new actual-π arithmetic source proves its signed bound and retains
the same child digit.

For reference, DC1 clips the inherited deficit `h_d=(-G_d)_+`, sets
`Y_d=D_d-h_d`, and applies the sharp regular-decagon envelope:

```text
q*Delta_0-21/10-hbar
  + gamma_10(hhat_1-(q/2)*P_1) > 0.                (DC1)
```

This corrected audited `proof sketch` preserves the same FMR witness, but its
uniform actual-π positivity closure is separated by the node above. It remains
a possible pathwise consumer when independent arithmetic selects favorable
nodes. Pair-π is no longer an active fallback.

This is a research target, not a proved theorem. See
[`FIRST_OPEN_PI_LEMMA.md`](knowledge/pi/active/FIRST_OPEN_PI_LEMMA.md).

## What is known and what is excluded

- A certified finite π seed and two replay levels show the consumer is
  non-vacuous, but finite data cannot provide unbounded transport.
- T190 is machine-checked, but no useful complementary actual-π rank premise
  is known on an unbounded reached path.
- An actual positive pi node makes all five Pair margins and the DC1 premise
  negative while full FMR holds uniquely; low-sector uniform closures miss
  the required coherent multi-sector same-child interference.
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
