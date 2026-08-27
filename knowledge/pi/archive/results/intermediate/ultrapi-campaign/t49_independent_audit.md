# T49 independent audit

Date: 2026-08-12 UTC  
Target: `TheoryLib/PiQuantitativeBlockHitting/T49T49MachinEndpointPulse.lean`  
Target SHA-256: `a5ee98d8842508eb81b8d8fd660441b5e0e5a4cef407318ad125d43d40249077`  
Problem source: `problems/local/pi-digits.txt`  
Problem-source SHA-256: `2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825`

Status: `machine-checked`. No mathematical, quantifier, indexing, cancellation,
or axiom-audit error was found in the audited T49 claim. This status applies
only to T49's exact rational and p-adic pulse statements; it is not a claim
about decimal recurrence, normality, or occurrence of every finite word in
pi.

## Exact quantifiers and claim

The final theorem quantifies over `N p t : Nat` and assumes

- `p.Prime`, `12 < p`, `p != 239`, and `p != 317`;
- `p = 12*N + 17`;
- `t <= 2*N + 1`.

It concludes

`padicValRat p (sampledMachinValueRat (N + 2 + t)) = -1`.

This is neither an existence theorem for such primes nor a decimal-cylinder
theorem. The `p != 239` hypothesis is conservative (it already follows from
`p = 12*N+17` by reduction modulo 12), while `p != 317` is load-bearing:
`951 = 3*317` is the exceptional localized cancellation factor.

## Endpoint and cancellation audit

The two singular terms are indexed correctly.

- In forcing block `N`, base-239 slot `j=5` has exponent
  `12*N+7+2*5 = 12*N+17 = p` and signed coefficient
  `4*(-1)^5 = -4`.
- In forcing block `N+1`, base-5 slot `j=0` has exponent
  `12*(N+1)+5 = 12*N+17 = p` and coefficient `16`.
- The two-step recurrence is
  `y_(N+2) = 100*y_N + 10*f_N + f_(N+1)`. Including the powers of ten
  already present in `f_N` and `f_(N+1)`, multiplication by `p` therefore
  gives the exact core
  `10^(N+2) * (16/5^p - 4/239^p)`.

Fermat localization gives

`16/5 - 4/239 = (16*239 - 4*5)/(5*239) = 4*951/(5*239)`.

For the admitted primes, `5`, `239`, `10`, and `4*951` are nonzero modulo
`p`. The prior sample and both endpoint-regular blocks are p-integral. Thus
the explicit core has valuation zero, the correction after multiplication
by `p` has valuation at least one (or is zero), and the correction cannot
cancel the core. The conclusion `v_p(y_(N+2)) = -1` follows with the correct
sign.

## Off-by-one audit of the propagation window

For an intervening forcing index `N+2+u` with `u <= 2*N`, the base-5
exponents range from `p+12` through `36*N+39`, and the base-239 exponents
range from `p+14` through `36*N+41`. All are odd and strictly between `p`
and `3*p = 36*N+51`; the sole possible intermediate multiple, `2*p`, is
even. Hence every such forcing block is p-integral.

The accumulation for offset `t` uses exactly `u < t`. Therefore
`t <= 2*N+1` implies `u <= 2*N`, exactly as required. At the first omitted
offset `t = 2*N+2`, the new forcing has `u=2*N+1`, hence block index
`3*N+3`, and it contains exponent `3*p` twice:

- base-5 slot `j=5`: `12*(3*N+3)+5+10 = 3*p`;
- base-239 slot `j=4`: `12*(3*N+3)+7+8 = 3*p`.

Thus there is no off-by-one error: `2*N+1` is the last offset covered by
the proof's p-integral-forcing argument. It is not asserted to be the last
offset at which valuation `-1` happens.

As an `experiment`, exact rational evaluation for
`(N,p) = (0,17), (1,29), (2,41), (3,53), (6,89), (7,101), (8,113),
(10,137)` returned valuation `-1` at every stated offset. The first offset
beyond the theorem also returned `-1` in these finite cases; that finite
observation neither extends nor contradicts the theorem, because the
integrality premise first fails there.

## Declarations, forbidden constructs, and axiom coverage

The file contains exactly 4 definitions and 35 propositions (lemmas or
theorems). A token scan found no `sorry`, `admit`, `native_decide`, custom
`axiom`, `unsafe`, or `opaque` declaration. `noncomputable section` is the
ordinary classical wrapper and is not a forbidden proof shortcut.

All 35 propositions are present exactly once in `audit/AxiomAudit.lean`;
the declaration-to-registration comparison found no missing or extra T49
name. Definitions do not require `#print axioms` registration. An independent
probe of all 35 propositions reported only the allowlisted dependencies
`propext`, `Classical.choice`, and `Quot.sound` (two elementary divisibility
lemmas do not use `Classical.choice`).

Verification performed:

```text
lake build TheoryLib.PiQuantitativeBlockHitting.T49T49MachinEndpointPulse
  passed: 8566 jobs

lake env lean audit/AxiomAudit.lean
  passed

T49 declaration/audit comparison
  declared propositions: 35
  registered propositions: 35
  missing: []
  extra: []
```

Subsequent integration result: the coordinating agent ran the repository-wide
`scripts/check.ps1` gate after T49 and T50 settled. It completed all 8,493 jobs
and passed the kernel build, exploit scan, and exact-allowlist axiom audit on
2026-08-12 UTC.
