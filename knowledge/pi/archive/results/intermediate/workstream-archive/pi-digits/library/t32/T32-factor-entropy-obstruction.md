# T32 factor-complexity and entropy obstruction

Status: `machine-checked` for the named Lean theorems in
`FactorEntropyObstruction.lean`. This is a conditional obstruction, not a
resolution of the open pi statements.

## Source and target

The immutable canonical source is `knowledge/pi/statements/pi-digits.txt`, with
SHA-256
`2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825`.
Its canonical V1 asks whether every finite decimal word, including words with
leading zeroes, occurs contiguously in the decimal expansion of pi. T7 defines
that proposition as `Theory.PiDigits.V1` and its exact stream as
`Theory.PiDigits.piDigit`.

The quantifiers formalized here are:

- `s : Nat -> Fin 10` is any one-sided decimal stream.
- `k > 0` is the length of a fixed block `w : Fin k -> Fin 10`.
- `OmitsBlock s w` means there is no starting position where `w` occurs.
- `m >= 1` is arbitrary; factors have length exactly `m*k`.
- Factors may start at every natural-number position, not only at multiples of
  `k` and not only at the beginning of the stream.

The empty word is not treated as an obstruction: it occurs at every position,
and the exact T7 bridge proves that a missing T7 word necessarily has positive
length.

## Definitions

T11 imports T1's generic `Factor` and `canonicalFactorComplexity` definitions
and defines the pi specialization `piFactorComplexity`. All three are reused
rather than duplicated:

```text
Factor s n
canonicalFactorComplexity s n = Nat.card (Factor s n)
piFactorComplexity n = canonicalFactorComplexity piDigit n
```

The delivered file defines the full positive-length factor entropy by

```text
factorEntropyTerm s n = log(p_s(n+1)) / (n+1)
factorEntropy s = limsup_{n -> infinity} factorEntropyTerm s n,
```

where `p_s(N) = canonicalFactorComplexity s N`. The shift by one excludes only
the zero-length factor and therefore is the standard full-length limsup, not a
limsup sampled only at multiples of `k`.

## Finite counting proof

Fix `w` of length `k > 0` and suppose `s` omits `w`. A factor `v` of length
`m*k` has the ordered consecutive chunks

```text
v[r*k], v[r*k+1], ..., v[r*k+k-1]    for 0 <= r < m.
```

Every such chunk is itself a factor of `s`: if `v` occurs at position `i`, its
`r`th chunk occurs at `i+r*k`. Consequently no chunk equals `w`.

There are exactly `10^k` functions `Fin k -> Fin 10`, and exactly one is `w`,
so there are `10^k-1` allowed chunks. The map from `v` to its ordered `m`-tuple
of chunks is injective. For a coordinate `q < m*k`, division by positive `k`
recovers

```text
r = q / k,   j = q % k,   q = r*k+j.
```

Thus equality of all chunks gives equality at every coordinate of the original
factor. Taking finite cardinalities proves

```text
p_s(m*k) <= (10^k-1)^m.
```

This is theorem
`Theory.PiDigits.T32.factorComplexity_mul_le_pow_of_omits`. Its statement
contains the requested hypotheses `k > 0` and `m >= 1` explicitly.

## Full limsup entropy proof

Set `A = 10^k-1`. For an arbitrary positive length `N`, let
`q = floor(N/k)`. Then

```text
N <= (q+1)k.
```

The generic canonical factor complexity imported through T11 is monotone in
length, because deleting the last symbol maps length-`n+1` factors onto
length-`n` factors. Applying the finite theorem at `m=q+1` gives

```text
p_s(N) <= p_s((q+1)k) <= A^(q+1).
```

Every factor set is nonempty (the factor starting at zero exists), so its
cardinality is at least one and all logarithms used below are of positive
numbers. Since `q <= N/k` and `log A >= 0`,

```text
log p_s(N) / N
  <= (q+1) log A / N
  <= log A / k + log A / N.
```

The final term tends to zero as `N` tends to infinity. The Lean proof compares
the full entropy sequence with this convergent upper envelope using
`Filter.limsup_le_limsup`, yielding

```text
factorEntropy s <= log(10^k-1) / k.
```

This is theorem `Theory.PiDigits.T32.factorEntropy_le_of_omits`.

Finally, `k > 0` implies

```text
0 < 10^k-1 < 10^k.
```

Strict monotonicity of the real logarithm and
`log(10^k) = k*log 10`, followed by division by positive `k`, give

```text
log(10^k-1) / k < log 10.
```

This is theorem
`Theory.PiDigits.T32.omittedBlock_entropyBound_lt_logTen`.

## Exact T7 specialization

The theorem
`Theory.PiDigits.T32.not_canonicalV1_iff_exists_omitted_nonemptyBlock`
proves the literal equivalence

```text
not Theory.PiDigits.V1
  iff
exists k > 0, exists w : Fin k -> Fin 10,
  OmitsBlock Theory.PiDigits.piDigit w.
```

The forward direction negates T7's quantifiers directly. A missing list cannot
be empty, because negated occurrence supplies an index below its length. The
list is converted extensionally to `Fin list.length -> Fin 10`. The reverse
direction converts a block to `List.ofFn`; a T7 occurrence of that list would
be an occurrence of the supposedly omitted block.

The theorem
`Theory.PiDigits.T32.not_canonicalV1_implies_factorEntropy_deficit` then
specializes the generic bounds to T11's exact `piFactorComplexity`. Its sole
hypothesis is `not Theory.PiDigits.V1`; it concludes the existence of one
positive `k` and one omitted word witnessing both the finite bounds and the
strict full entropy deficit.

## Scope

This conditional obstruction proves neither V1 nor its negation for pi. It
also proves neither sibling V3 nor its negation for pi. In particular, the
file contains no unconditional assertion that pi omits a word, has an entropy
deficit, satisfies V1, fails V1, satisfies V3, or fails V3.

## Reproduction and axioms

From the workspace root:

```bash
mkdir -p .lake
ln -sfn /opt/allmath-lean/.lake/packages .lake/packages
lake build TheoryLib.PiDigits.T11PiDigitFactorComplexity
lake env lean removed-workflow-record://todo-theory-pi-digits-t32-1784704435-r0/theory_artifacts/FactorEntropyObstruction.lean
```

The file prints the axioms of the five principal theorems. Local recompilation
reports only `propext`, `Classical.choice`, and `Quot.sound`; it uses no
`sorry`, `admit`, `native_decide`, new axiom, unsafe declaration, or
compiler-trusting shortcut.
