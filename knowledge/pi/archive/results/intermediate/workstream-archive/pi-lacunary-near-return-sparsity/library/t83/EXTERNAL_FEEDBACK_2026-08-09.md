# External expert feedback supplied 2026-08-09

Status: `conjecture` and audit input only. Two independent reviewers supplied
these claims through Marcel without access to the repository, Lean files, or
axiom audit. Nothing here is machine-checked or a reviewer disposition.

## Agreed audit claims

1. A continuous non-Lebesgue `T_10`-invariant probability measure has a
   nonzero persistent Fourier ray because invariance gives
   `mu_hat(10 h) = mu_hat(h)`, while Wiener's lemma gives vanishing
   cardinality-normalized bulk mean-square energy. Nonuniform iid decimal
   digits give an explicit full-support ergodic example; generic points are
   claimed to yield finite empirical-orbit approximants. This is not a claim
   about the orbit of `pi`.
2. At `L_n = 10^(floor(n/2))`, positive entropy is claimed to follow from the
   long-sector estimate `R_pi(n,L_n) <= L_n * 10^(o(n))`; the elementary
   `O(n L_n)` short sector is exponentially negligible in the resulting
   Cauchy--Schwarz lower bound for block complexity.
3. T79's least-valuation argument requires a tie audit. For
   `P = 147153121`, a claimed first exceptional configuration uses terminal
   exponent `P^2+2`: the terms with exponents `P^2` and `P^2+2` allegedly have
   the same minimum `P`-adic valuation. The normalized leading residue is
   claimed nonzero at this tie, but later ties were not checked.
4. The relevant modular cancellation regime is claimed to be
   `N asymp log q`, not a universal square-root-modulus frontier. Some
   prime-power recurrence estimates beat square root at subpower lengths but
   remain far above logarithmic length. A modulus-only logarithmic-length
   theorem is impossible for all numerators because a small numerator and
   sufficiently large modulus place the geometric progression in a short arc.

## Conflicting short-sector claims

Review A claims arbitrary infinite words can realize order `n L_n` exact
short-sector equal-block collisions by inserting dominant constant runs. It
also says this does not obstruct positive entropy under the long-sector bound.

Review B claims that for any word over an alphabet of size `b`, with
`L = b^(floor(n/2))`, the ordered exact-equality counts satisfy

`S_(n,L) <= C_b L + (3/2) R_(n,L)`.

Its proposed proof bins starts into intervals of length `n`, separates bins by
parity, and bounds high within-bin multiplicity using the number of words with
a period at most `floor((n-1)/(k-1))`. This may fail through endpoint,
separation, multiplicity, or statistic mismatches and must be proved or
falsified rather than trusted.

The audit must first identify the exact program-qualified T56/C7 statistic:
exact block equality, neighboring cylinders, or a carry-thickened relation.
The two claims above concern exact block equality and do not automatically
transfer to a broadened relation.

## Additional proposed identities

- The exact ray defect is
  `|mu_N_hat(10^r h) - mu_N_hat(h)| <= 2r/N`; all-`N` versus selected-`N`,
  fixed versus growing `h`, and `r/N` quantifiers determine whether a terminal
  condition is equivalent to Weyl cancellation or weaker/stronger.
- Cylinder energy admits a cyclic discrete-Fourier alias expansion in additive
  classes `k + ell*10^m`, not multiplicative decimal rays. Smoothing leaves a
  boundary-occupancy term which is another fixed-`pi` near-return statistic.
- A T29 weighted square function expands into a positive kernel on differences
  `10^k(10^r-1)` and may be a repunit near-return restatement rather than an
  independent frontier.

Every statement in this memo remains unverified until independently replayed,
proved, or falsified. No C1, C2, ENT, LL, normality, equidistribution, or new
fact about `pi` follows merely from the feedback.
