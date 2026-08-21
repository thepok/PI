# Independent adversarial audit: T62 Hutton eligible-prime product

Audit time: 2026-08-12T13:36:23Z.

Claim label: `machine-checked` for the exact finite-set, individual-prime,
coprimality, and product-divisibility declarations below. This is not a
prime-number-theorem claim and not a decimal-block claim about pi.

## Verdict

**PASS.** I found no defect in the T62 statement or proof. The eligible set
has exactly the hypotheses required by T61, including both interval
endpoints; the odd-index witness is valid; distinct eligible primes are
pairwise coprime; the generic finite-product lemma correctly handles its
empty and nonempty cases; and the final product-divisibility theorem follows
without an unstated positivity or nonemptiness assumption.

The focused source, aggregate `TheoryLib` target, direct axiom audit, exact
small-case audit file, and full repository verification gate all passed. The
module has nine declarations (two definitions and seven theorems), and all
nine are printed exactly once in `audit/AxiomAudit.lean`. Every declaration
reports only the exact allowlist `propext`, `Classical.choice`, and
`Quot.sound`. No formal edit was required during this audit.

## Exact normalized statement

Let

```text
R_K = 4*K + 3,
S_K = {p natural : p is prime, 7 < p, p != 17,
                     R_K < 2*p, p <= R_K},
P_K = product of p over p in S_K.
```

T62 defines `S_K` as a filtered `Finset.range (4*K+4)` and proves

```text
p in S_K  iff
  p.Prime and 7 < p and p != 17 and
  4*K+3 < 2*p and p <= 4*K+3.
```

For each `p in S_K`, T62 packages the odd witness `p = 2*k+1`, invokes T61,
and obtains

```text
p divides den(huttonLowerRat K),
padicValNat p den(huttonLowerRat K) = 1.
```

Finally it proves

```text
P_K divides den(huttonLowerRat K).
```

The last conclusion is divisibility only. It does not say that the complete
denominator equals `P_K`, nor that the quotient is coprime to `P_K`.

## Quantifier and endpoint audit

`Finset.range (4*K+4)` means exactly `p < 4*K+4`, which is equivalent over
natural numbers to `p <= 4*K+3`. The filter contributes precisely

```text
p.Prime, 7 < p, p != 17, 4*K+3 < 2*p.
```

Thus membership is exactly the T61 scope, with no missing or strengthened
hypothesis. In the notation `R=4*K+3`, this is the upper-half interval

```text
R/2 < p <= R,
```

or equivalently `R < 2*p <= 2*R`. The endpoint `p=R` is included when it is
prime; for example, `K=2` gives `R=11` and includes `p=11`. The lower endpoint
is strict exactly as in T61. The exceptional prime `17` is explicitly
removed even when it lies in the interval; for example, at `K=4` the set is
`{11,13,19}`, not `{11,13,17,19}`.

Every eligible prime is greater than seven and hence unequal to two. The use
of `Prime.odd_of_ne_two` and the witness `k=p/2` therefore gives
`p=2*k+1` with no parity gap. This is the explicit index hypothesis required
by T61.

## Coprimality and product proof audit

For distinct members `p,q` of `S_K`, membership supplies primality for both,
and `Nat.coprime_primes` turns `p != q` into `Nat.Coprime p q`. This proves
the exact `Set.Pairwise Nat.Coprime` premise used by the generic product
lemma.

The induction in `finset_prod_id_dvd_of_pairwise_coprime` is sound:

- The empty product is `1`, so the base case is `1 divides n`.
- In the insertion case, pairwise coprimality proves that the new element is
  coprime to the product of the old set.
- The hypotheses give both the new-element divisor and, by induction, the
  old-product divisor.
- `Nat.Coprime.mul_dvd_of_dvd_of_dvd` then yields divisibility of the combined
  product.

The argument does not require `n>0`, nonempty `S`, or a separate positivity
hypothesis. Applying it to `S_K` and the reduced Hutton denominator is
therefore valid for every natural `K`, including small `K` with `S_K` empty.

The multiplicity theorem remains correctly scoped per eligible prime. T62
does not overstate it as an exact factorization of the whole denominator.

## Independent exact finite checks

The separate Lean file
`work/ultrapi-resume/t62_independent_checks.lean` uses kernel reduction and
`norm_num` only (no `native_decide`). It proves the following boundary cases:

| `K` | `R=4K+3` | exact eligible set | product |
|---:|---:|---|---:|
| 0 | 3 | empty | 1 |
| 1 | 7 | empty | 1 |
| 2 | 11 | `{11}` | 11 |
| 3 | 15 | `{11,13}` | 143 |
| 4 | 19 | `{11,13,19}` | 2717 |

It also kernel-checks the exact reduced denominators

```text
den(H_0) = 27783,
den(H_2) = 19265262529822155,
den(H_4) = 179980826858896989916014909885.
```

The file proves `11 | den(H_2)`, `2717 | den(H_4)`, and independently checks
that `11^2` does not divide `den(H_2)` and none of `11^2`, `13^2`, or `19^2`
divides `den(H_4)`. These finite checks corroborate the endpoint, exclusion,
product, and multiplicity behavior, but the general result rests on the Lean
proof in T62 rather than on finite evidence.

## Registration, forbidden constructs, and build evidence

`TheoryLib.lean` imports T62 exactly once, and `audit/AxiomAudit.lean` imports
it exactly once. The audit file contains exactly nine T62 registrations, one
for each declaration:

```text
huttonEligiblePrimeSet
huttonEligiblePrimeProduct
mem_huttonEligiblePrimeSet_iff
huttonEligiblePrime_exists_oddIndex
huttonEligiblePrime_dvd_huttonLowerRat_den
padicValNat_huttonLowerRat_den_huttonEligiblePrime
huttonEligiblePrimeSet_pairwise_coprime
finset_prod_id_dvd_of_pairwise_coprime
huttonEligiblePrimeProduct_dvd_huttonLowerRat_den
```

Commands run against the audited source:

```text
lake env lean TheoryLib/PiQuantitativeBlockHitting/T62T62HuttonEligiblePrimeProduct.lean
  exit 0; all nine declarations report only
  [propext, Classical.choice, Quot.sound]

lake build TheoryLib.PiQuantitativeBlockHitting.T62T62HuttonEligiblePrimeProduct
  exit 0; focused target and dependencies completed successfully (8569 jobs)

lake build TheoryLib
  exit 0; aggregate TheoryLib build completed successfully (8766 jobs)

lake env lean audit/AxiomAudit.lean
  exit 0; all nine T62 registrations report only the exact allowlist

lake env lean work/ultrapi-resume/t62_independent_checks.lean
  exit 0

pwsh -File scripts/check.ps1
  exit 0; PASS: kernel build, exploit scan, and exact-allowlist axiom audit
  succeeded

git diff --check -- T62 module, check file, TheoryLib.lean, audit/AxiomAudit.lean
  exit 0
```

A focused source scan found no `sorry`, `admit`, `sorryAx`, `native_decide`,
new `axiom`, `opaque`, `constant`, `unsafe`, `implemented_by`,
`Lean.ofReduceBool`, or `Lean.trustCompiler` construct in T62.

Point-in-time SHA-256 hashes:

```text
2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825  problems/local/pi-digits.txt
5ed4419d962534b4e476e00187e6dcbd045b2cb1b048e8f6309b401728597ab8  TheoryLib/PiQuantitativeBlockHitting/T62T62HuttonEligiblePrimeProduct.lean
51e88925d7e9d959ed5450bd2985645e0e5edfb4d27631c0da28aa4e53cd2a11  work/ultrapi-resume/t62_independent_checks.lean
051c2e3c75a054db16aa2f3fe4d82ee1364c621deec3f97cf2eaed6c1db57e4a  TheoryLib.lean
2801d871bbdf79d5171a7e8b6496b39f2b1a4030e41e476c29c55a7dc3e1f475  audit/AxiomAudit.lean
```

## No PNT or V1 conclusion

T62 proves an exact finite divisor for each `K`; it proves no lower bound,
asymptotic, or divergence result for `P_K`. In particular, it does not use or
formalize the prime number theorem, Chebyshev estimates, Bertrand's postulate,
or any statement that the product grows exponentially.

Even a later lower bound on `P_K` would concern the reduced denominator and
eventual period of a rational Hutton shadow. It would not by itself locate a
prescribed decimal word within the finite prefix certified by the Hutton
approximation, establish discrepancy, or prove that every finite decimal word
occurs in pi. T62 is supporting `machine-checked` denominator infrastructure,
not a `candidate resolution` or `verified resolution` of V1.
