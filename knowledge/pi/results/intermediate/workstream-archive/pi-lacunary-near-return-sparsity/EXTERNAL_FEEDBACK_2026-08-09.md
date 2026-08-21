# Two independent expert reviews supplied 2026-08-09

Status: **review commentary** supplied by Marcel.  Neither reviewer inspected
the repository, Lean declarations, axiom audit, or full T-number artifacts.
This memo is untrusted research input: it promotes no claim and every proposed
formula must be independently replayed or proved.

## Points of agreement worth auditing

Both reviews agree that the project is a reduction/obstruction program, not a
new theorem about the decimal digits of `pi`.  They independently propose:

1. a realizable upgrade of T67: every continuous non-Lebesgue
   `T_10`-invariant measure has a nonzero persistent decimal Fourier ray,
   while Wiener's lemma makes its cardinality-normalized bulk mean-square
   Fourier energy tend to zero; a nonuniform Bernoulli decimal measure gives
   an explicit full-support ergodic example, and generic points give genuine
   finite empirical-orbit approximants;
2. the positive-entropy endpoint does not require removal of the elementary
   `O(n L_n)` short-sector contribution at
   `L_n = 10^(floor(n/2))`: a long-sector bound
   `R_pi(n,L_n) <= L_n * 10^(o(n))` already yields entropy exponent at least
   `1/2`; formalize the exact quantifiers and normalization before retaining
   C7 as an ENT frontier;
3. T79 needs an adversarial valuation-tie audit.  Factors such as `2k+1` can
   make two arctangent terms share the least `P`-adic valuation.  The supplied
   candidate first tie uses `P = 147153121`, terminal exponent `P^2+2`, and
   claims a nonzero normalized residue at that tie.  This is an audit warning,
   not an established error or repair;
4. the useful arithmetic frontier is not generically “square-root modulus.”
   Prime-power recurrence estimates can reach subpower lengths, but known
   bounds still miss the audited regime `N asymp log q`; no modulus-only
   theorem can work there because suitable numerators put all phases in a
   short arc.  Any route must exploit the specific reduced numerator;
5. cylinder energy has an exact cyclic-DFT/ordinary-Fourier alias expansion in
   additive classes `k + ell*10^m`, while decimal rays are multiplicative.
   Smoothing leaves a boundary-occupancy term that is itself a fixed-`pi`
   near-return problem.  T29 likewise expands into a positive Fejer kernel on
   repunit differences `10^k(10^r-1)` and may not be an independent frontier.

## Material disagreement requiring falsification

The reviewers disagree about the exact-equal-block short sector.

- Review A says arbitrary infinite words can realize order `n L_n` through
  dominant constant runs; it emphasizes that this is nevertheless
  exponentially harmless for ENT.
- Review B proposes the stronger finite-word inequality
  `S_(n,L) <= C_b L + (3/2) R_(n,L)` at
  `L = b^(floor(n/2))`, using length-`n` bins, parity-separated long pairs,
  and a period-dictionary bound on high within-bin multiplicity.

Do not choose by authority.  First normalize endpoint conventions and whether
T56/C7 counts exact block equality, neighboring cylinders, or a thickened
carry relation.  Then either prove the proposed finite-word inequality,
produce a finite counterexample family, or isolate the exact extra hypothesis
under which it holds.  Even if it fails, separately prove the weaker
subexponential ENT criterion, which does not need it.

## Other proposed checks

- Classify terminal-ray conditions using the exact defect
  `|mu_N^(10^r h)-mu_N^(h)| <= 2r/N`, with all-`N` versus selected-`N`, fixed
  versus growing `h`, and `r/N` quantifiers explicit.
- Reproduce T97's constant and complete critical-band union before describing
  its almost-everywhere closure as independently checked.
- Consider a genuinely weaker fixed-`pi` target such as linear complexity
  `p_pi(n) >= (1+delta)n`, but do not claim that the current scalar
  irrationality measure supplies it.

## Claim discipline

All statements above are proposed `conjecture` or audit inputs until checked.
The external reviewers' agreement is not independent verification of local
artifacts.  No C1, C2, ENT, LL, normality, equidistribution, or new theorem
about `pi` follows from these reviews.
