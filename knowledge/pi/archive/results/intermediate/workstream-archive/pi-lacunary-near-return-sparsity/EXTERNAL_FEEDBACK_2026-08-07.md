# External strategic feedback (2026-08-07)

Status: **review commentary** supplied by Marcel from a mathematician; this is
not a human-only reviewer disposition, a proof verification, or a claim-status
promotion.

## Verdict

The reduction/obstruction/falsification program is mathematically sensible,
but the terminal top-shell condition is not yet credible leverage on the
fixed-`pi` problem.  Along a decimal frequency ray,

\[
  |\widehat\mu_N(10^r h)-\widehat\mu_N(h)|\le 2r/N,
\]

so a terminal condition with `r = o(N)` may simply re-express fixed-frequency
Weyl cancellation.  Bulk shell averages can additionally dilute a persistent
sparse decimal ray.  Coefficient algebra and additional finite values of the
shell statistic therefore should not be treated as a route across the fixed-
`pi` boundary.

## Requested sanity checks and repository coverage

The reviewer asked for:

1. an exact implication diagram among the terminal condition,
   equidistribution, discrepancy, block-collision excess, and weak/full pair
   correlation;
2. counterexamples to failed converses, especially sparse-ray concentration
   and bulk-shell dilution;
3. the exact decimal Walsh/cylinder identity equating block-frequency `L2`
   error with excess collision mass;
4. random controls preserving the multiplier-10 orbit coupling, plus
   adversarial nonnormal controls; and
5. a genuinely `pi`-specific arithmetic representation of the same frontier.

Items 1--3 are already covered by accepted T60 and, on its exact formal
domain, machine-checked T67.  Earlier calibration work covers the methodological
point in item 4; it must not be reopened merely to accumulate more values of
the same statistic.  Item 5 is the only current research lane and is the
purpose of T78's bounded Euler--Rabinowitz--Wagon factorial-expansion audit.

## Strategic effect

This feedback independently supports the current direction guard: do not
schedule more stopping-rule algebra, generic metric lacunary results, shell
reformulations, or experiments whose output is only that `pi` looks random.
Accept future work only if it supplies a quantitative `pi`-specific bridge or
a family-specific obstruction.  No theorem about fixed `pi`, normality,
equidistribution, C1, or C2 follows from this feedback.

## Trust-boundary cautions from the reviewer

The reviewer explicitly could not verify from the earlier summary alone:

- the individual Lean theorem statements;
- the factor-4 normalization used in the reduction; or
- the admissibility and endpoint handling of the T57 minimizer.

These are not reviewer-discovered errors. They are reminders that a green
Lean build validates only the encoded implication, not that the terminal
hypothesis is weaker than the desired conclusion or that the encoding is the
intended analytic object. T57 remains a `proof sketch`; its conclusions must
not be reported as machine-checked. T67 is `machine-checked` only for the
named declarations and explicitly confines its sparse-ray/bulk-shell
separators to an abstract cutoff array with no orbit-realizability claim.

## Detailed methodological constraints retained

- A single near return is essentially pigeonhole-scale evidence and has no
  normality consequence without multiplicity or aggregate-energy control.
- A bulk shell average can dilute one persistent decimal ray. Any future
  terminal estimate must expose whether it is pointwise/per-ray,
  unnormalized-positive, or Carleson/supremum type.
- Random controls must preserve the multiplier-10 coupling
  `e(10 h x_n) = e(h x_(n+1))`; independent phase randomization is not the
  relevant null model. Signed ratios must not be presented as evidence for a
  nonnegative target.
- Finite experiments should compare distributions and adversarial digit
  streams, not nested ranges as independent samples. They remain
  `experiment`, never asymptotic evidence.
- Almost-everywhere lacunary or additive-energy theorems are useful only for
  normalization and calibration. They do not specialize to fixed `pi`.
- Irrationality-measure and naive rational-approximation routes have an
  exponential scale mismatch with the polynomial orbit length. A future
  arithmetic proposal must overcome that mismatch quantitatively rather than
  merely invoke finite-field exponential-sum machinery.

The local coverage is deliberately split: T60 is a `proof sketch` containing
the full implication/counterexample audit and the exact Walsh identity; T67
machine-checks the finite Walsh/cylinder identity and abstract separator
statements. Neither establishes fixed-`pi` cancellation. T78 subsequently
performed the requested bounded audit of one genuinely `pi`-specific
factorial representation and found a family-specific square-root-modulus
obstruction, again only as a `proof sketch`.
