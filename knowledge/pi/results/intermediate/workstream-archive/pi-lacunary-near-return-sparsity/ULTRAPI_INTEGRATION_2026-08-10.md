# Ultrapi integration snapshot — refreshed 2026-08-12 UTC

Status: mixed `machine-checked`, `proof sketch`, and review commentary as
identified below. This memo is an operator-requested cross-program handoff,
not an orchestrator result and not an independent expert review.

## Provenance and verification

- Source research dossier: `ultrapi.md`
- Dossier SHA-256 at the 2026-08-12 refresh:
  `b7f38539dedc175ad47035c3aafdb566b2d67c461b8df9b63130667d67393872`
- Earlier 2026-08-10 snapshot SHA-256:
  `c2d9dffb67b0a5416aa55124ebc5af0174990909a47eae54f91092fe4096d011`
- Formal source range:
  `TheoryLib/PiQuantitativeBlockHitting/T18*.lean` through
  `TheoryLib/PiQuantitativeBlockHitting/T70*.lean`
- The modules are imported by `TheoryLib.lean`; every supporting declaration
  is registered in `audit/AxiomAudit.lean`.
- On 2026-08-10, T42 and T43 were independently recompiled locally and the
  complete axiom audit was replayed. The only reported dependencies were the
  repository allowlisted logical axioms such as `propext`,
  `Classical.choice`, and `Quot.sound`. A forbidden-token scan found no
  `sorry`, `admit`, new `axiom`, `unsafe`, or `native_decide` in T42/T43.
- The repository-wide deterministic Lean gate that completed after T42/T43
  were added passed all 8,743 jobs. A separate `scripts/check.ps1` replay on
  2026-08-10 also passed the kernel build, verified-track exploit scan, and
  exact-allowlist axiom audit.

The formal implications encoded in T18--T43 therefore carry the label
`machine-checked`. This does not establish novelty, the intended every-word
statement, normality, equidistribution, C1, or C2. Claims described only in
`ultrapi.md` remain `proof sketch` unless a named Lean declaration proves the
exact statement.

## Results future directors must consume

The T18--T43 intake below remains valid. The 2026-08-12 refresh adds the
T44--T70 results summarized afterward. A director must treat both ranges as
consumed prior work. In particular, it must not rediscover a later theorem
merely because the original 2026-08-10 hash and range stopped at T43.

### Natural-scale sufficient condition (T18--T19)

T18 and T19 sharpen the finite Fourier certificate for hitting every decimal
cell at depth `k`: the usable cutoff is `2 * 10^k`, with the dossier's exact
threshold

`1 / (24 * 10^k) + 1 / (12 * 10^(3*k))`.

This is a strictly weaker sufficient hypothesis than the earlier T6
certificate, but it remains an unproved fixed-pi cancellation hypothesis. Do
not report it as a proof that any new word occurs in pi.

### Unconditional additive Fourier information (T20--T29)

T20--T25 prove fixed-pi additive Fourier-defect statements. In particular,
for every fixed nonzero integer frequency `h` and every fixed real threshold
`A`, eventually

`A <= N - |sum_{j<N} exp(2*pi*i*h*10^j*pi)|`.

T24 makes this simultaneous on each fixed finite frequency window. T25 proves
the exact multiplier-ten transport identity and its boundary loss, so decimal
frequency shifts transport rather than amplify the additive defect.

T23--T28 obtain natural-frequency information at the least prefix containing
all first occurrences: at least one sixteenth of frequencies through `10^m`
have additive gap at least `p_pi(m) / 32`. T29 records the relative saving
that an additional appearance-ratio hypothesis would give.

These are genuine `machine-checked` fixed-pi statements, but the word
*additive* is decisive. They provide no control of the ratio of the gap to
`N`; sparse-digit separators in the dossier show that an unbounded additive
gap alone is compatible with missing decimal words.

### Entropy and recurrent-language results (T30--T33)

T30 records the exact equivalence between maximal base-ten factor entropy and
the every-word property. It does not prove maximal entropy for pi.

T31--T32 prove `machine-checked` unconditional recurrent-language bounds:
the recurrent factor complexity of pi is at least `m + 1`, increases by at
least one per length, and at every length there is a recurrent right-special
factor with two recurrent continuations. T33 gives a sharp non-pi separator,
showing that generic aperiodicity, transcendence, or scalar irrationality
measure cannot improve these bounds abstractly.

### Rational/Machin transfer and its wall (T34--T43)

T34--T41 build an exact rational Machin approximation and symbolic transfer:

- one-sided recurrent cell shadows lose at most a factor two;
- oversampling controls decimal boundary loss;
- the rational Machin partial sums approach pi fast enough to reproduce each
  fixed-depth decimal block code under the explicitly stated Diophantine
  premise;
- the sampled Machin orbit is a summable coboundary perturbation of the pi
  orbit, so qualitative Weyl cancellation is equivalent rather than easier;
- every-word recurrence is exactly reformulated as recurrence of every Machin
  rational cell.

T40--T42 prove exact local denominator clearing and two-adic order-one facts
for the paired forcing blocks. The stronger complete-forcing valuation
`N + 4` is only a `proof sketch` in `ultrapi.md`; T42 explicitly does not
formalize it.

T43 is a `machine-checked` artificial separator: positive, geometric,
summable forcing with the same style of exact two-adic certificate can
converge to the rational fixed orbit at `1/3` and eventually avoid the zero
decimal cell. Hence positivity, summability, geometric decay, and the
two-adic forcing profile alone cannot prove recurrence or the every-word
conjecture.

### Complete Machin arithmetic and selector wall (T44--T57)

T44--T52 are `machine-checked` exact arithmetic for the actual Machin
forcing and seed. They establish the complete two-adic numerator valuation,
prime survival and multiplicity in progressively wider linear denominator
bands, the fixed-modulus telescope, endpoint pulse laws, and an exact
three-primary factor persisting across a nested schedule. These results are
substantive numerator/denominator information, not distribution theorems.

T53--T57 are `machine-checked` carry and phase-recombination results. They
show that the complementary quotient is the coarse decimal carry, that the
three-primary factor stays fixed or triples, and that the apparent nested
selector transports the residual phase by an invertible permutation rather
than contracting it. The full selected phase is reconstructed only after the
uncontrolled complementary coordinate is supplied. Therefore another local
valuation, power-of-three lift, or denominator-divisibility theorem is not a
new route unless it also controls that actual complementary phase.

### Hutton rational shadows and denominator saturation (T58--T68)

T58--T60 give a `machine-checked` rational Hutton bracket, an exact
conditional cylinder certificate, and the exact positive adjacent increment.
T61--T66 then prove exact surviving-prime products down to the one-fifth band,
the five-primary denominator exponent, and oddness of the reduced
denominator. T67 is a `machine-checked` obstruction: for the exact
`1/2 + 1/3` shadow, the decimal preperiod ends only after the rational bracket
is already wider than one decimal cell. T68 gives a `machine-checked`
infinite family with simultaneous, explicitly growing 3- and 7-primary
denominator exponents.

These results nearly saturate the available denominator radical but still
leave only a logarithmic transferable orbit and do not localize the selected
Archimedean numerator. The associated prime-number-theorem asymptotics,
leading-unit models, and several cross-index analyses remain `proof sketch`
or `experiment` exactly where the dossier says so. Do not promote them to
`machine-checked`, and do not schedule another denominator inventory without
a displayed numerator-sensitive estimate at the required orbit length.

### Fixed-times-sixteen and empirical-rigidity frontier (T69--T70)

T69 is a `machine-checked` conditional topological reduction. Under the
explicit published joint-orbit-density premise, decimal disjunctivity is
equivalent to the single fixed return

`16 * {pi} in closure({10^n * pi mod 1 : n >= 0})`.

It proves neither that return nor disjunctivity. BBP coordinates transfer the
same unknown return; they do not make it probabilistically independent.

T70 is a `machine-checked` conditional measure-to-topology bridge. A
probability measure supported on the decimal pi-orbit closure that is
times-ten ergodic, not mutually singular with its times-sixteen pushforward,
and contains one support point with dense joint times-ten/times-sixteen orbit
has full support and implies V1. The focused audit is
`work/ultrapi-resume/t70_empirical_rigidity_audit.md`; all nine declarations
are registered, and the reported axiom set is the repository allowlist.
Ergodicity, nonsingularity, and the dense-support-point premise remain
unproved for an empirical limit of pi.

## Consequences for the main research program

Treat the following fingerprints as consumed, not new directions:

1. unbounded additive Fourier defect at fixed or finite-window frequencies;
2. power-of-ten frequency shifting as an amplification mechanism;
3. first-occurrence representative cancellation without a density or
   appearance-time bound;
4. generic recurrent-complexity arguments from aperiodicity,
   transcendence, or scalar irrationality measure;
5. Machin positivity, summability, geometric decay, symbolic shadowing, or
   the local/two-adic forcing certificate by itself.
6. extending Machin or Hutton denominator prime bands without a
   numerator-sensitive short-orbit estimate;
7. nested three-primary selector lifts that retain the complementary phase;
8. BBP reweighting or the fixed-times-sixteen return as though it were weaker
   than V1; and
9. the T70 empirical-rigidity implication with ergodicity, nonsingularity, or
   dense support simply restated as an unproved premise.

The narrow surviving opportunities are:

- a relative, growing-window fixed-pi cancellation estimate strong enough for
  T19;
- quantitative control of the last-first-occurrence ratio or another genuine
  density/multiplicity input that upgrades T28/T29;
- an arithmetic theorem using the *specific complete Machin numerator*,
  including its moving archimedean residue, rather than only denominator
  valuations; or
- a direct fixed-pi entropy/all-cell-recurrence theorem;
- a numerator-sensitive cancellation theorem in the actual logarithmic
  modular-orbit regime; or
- a genuine proof of the T70 empirical nonsingularity/ergodicity package for
  one fixed-pi orbit limit, not another conditional reformulation.

No result in this handoff is a `candidate resolution` or `verified
resolution`.
