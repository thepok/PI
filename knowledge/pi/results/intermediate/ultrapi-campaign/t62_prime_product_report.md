# T62 eligible-prime product report

Status: `machine-checked` for the finite claims below.  This is not a proof of
V1 and contains no asymptotic estimate.

Source statement: `problems/local/pi-digits.txt`, SHA-256
`2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825`.

Formal module:
`TheoryLib/PiQuantitativeBlockHitting/T62T62HuttonEligiblePrimeProduct.lean`,
SHA-256
`5ed4419d962534b4e476e00187e6dcbd045b2cb1b048e8f6309b401728597ab8`.

## Exact finite result

For `R = 4*K+3`, `huttonEligiblePrimeSet K` is exactly the finite set of
natural primes `p` satisfying

```text
7 < p,  p != 17,  R < 2*p,  p <= R.
```

The module proves:

- every eligible `p` divides `(huttonLowerRat K).den`;
- every eligible `p` has exact denominator valuation
  `padicValNat p (huttonLowerRat K).den = 1`;
- distinct eligible primes are pairwise coprime;
- consequently, `huttonEligiblePrimeProduct K`, the product of all eligible
  primes, divides `(huttonLowerRat K).den`.

The joint theorem is
`huttonEligiblePrimeProduct_dvd_huttonLowerRat_den`.

## Registered declarations

Nine declarations are printed both in the module and in
`audit/AxiomAudit.lean`:

1. `huttonEligiblePrimeSet`
2. `huttonEligiblePrimeProduct`
3. `mem_huttonEligiblePrimeSet_iff`
4. `huttonEligiblePrime_exists_oddIndex`
5. `huttonEligiblePrime_dvd_huttonLowerRat_den`
6. `padicValNat_huttonLowerRat_den_huttonEligiblePrime`
7. `huttonEligiblePrimeSet_pairwise_coprime`
8. `finset_prod_id_dvd_of_pairwise_coprime`
9. `huttonEligiblePrimeProduct_dvd_huttonLowerRat_den`

`TheoryLib.lean` imports the module.

## Verification

The focused build passed:

```text
lake build TheoryLib.PiQuantitativeBlockHitting.T62T62HuttonEligiblePrimeProduct
Build completed successfully (8569 jobs).
```

The direct audit passed:

```text
lake env lean audit/AxiomAudit.lean
exit 0
```

Each T62 declaration reports only the allowlisted axioms `propext`,
`Classical.choice`, and `Quot.sound`.  A focused forbidden-construct scan found
no `sorry`, `admit`, `native_decide`, `unsafe`, `opaque`, or axiom declaration,
and the focused `git diff --check` passed.

## Research boundary

T62 combines T61's individual prime-survival results into one exact finite
divisor.  It does not estimate that product's growth, invoke the prime number
theorem, control decimal prefixes, force a decimal cylinder hit, or prove that
any word occurs in pi.
