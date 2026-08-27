# T33 recurrent-alphabet entropy threshold

Status: `machine-checked` for the named theorems in
`RecurrentAlphabetEntropy.lean`.

## Source and scope

The immutable source is `knowledge/pi/statements/pi-digits.txt`, SHA-256
`2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825`.
The canonical question V1 asks for every finite decimal word to occur
contiguously. T33 instead gives a conditional criterion for sibling V3, the
statement that every infinite decimal stream embeds as a subsequence.

No entropy lower bound for T7's pi digit stream is proved. In particular, the
artifact proves neither V1 nor V3 for pi unconditionally. The canonical and
sibling quantifiers are not interchanged.

## Normalized statement

For a stream `s : Nat -> Fin 10`, a digit is recurrent when it occurs at or
beyond every threshold. Let `r` be the cardinality of this recurrent set. T33
proves

```text
factorEntropy(s) <= log r.
```

Here `factorEntropy` is exactly T32's limsup over every positive factor length,
not a sampled subsequence of lengths. Generic V3 failure means at least one of
the ten digits is not recurrent, so `r <= 9` and the entropy is at most
`log 9`. Contraposition and T9's exact bridge give

```text
log 9 < factorEntropy(piDigit) -> Theory.PiDigits.V3.
```

The hypothesis is conditional; the file does not establish it for pi.

The sharpness stream is an artificial non-pi stream. Its alphabet is the image
of `Fin 9` in `Fin 10`, namely digits 0 through 8. Every finite `Fin 9` word
occurs after this embedding, its factor complexity is exactly `9^n` at every
length `n`, and its entropy is exactly `log 9`. It fails generic decimal V3
because decimal digit 9 never occurs. It is formally distinct from T7's pi
stream: the constructed stream starts with 0, while the exact floor-based pi
stream starts with 1.

## Imported results

- T9 supplies the equivalence between generic V3 and arbitrarily late
  occurrence of every decimal digit, together with the exact T7 V3 bridge.
- T22 supplies `concatStream` and
  `enumeratedBlock_occursAt_concatStream`; these are reused for the universal
  nine-symbol stream.
- T32 supplies `factorEntropyTerm`, `factorEntropy`, positivity of factor
  complexity, and the established factor-complexity interface.
- T13 supplies existence of an arbitrarily late symbol in every stream over a
  finite alphabet.

None of these prior results is reproved.

## Finite transient prefix

For every nonrecurrent digit, negating recurrence gives a cutoff beyond which
that digit is absent. Taking the maximum over the finite decimal alphabet
gives one `C` after which every stream value is recurrent.

A length-`n` factor is encoded in one of two ways. If all its symbols are
recurrent, it is a word over the recurrent alphabet. Otherwise its first
occurrence starts before `C`, because an occurrence starting at or after `C`
could contain only recurrent symbols. This gives the injective count

```text
p_s(n) <= C + r^n <= (C + 1) r^n.
```

Since every stream has `r >= 1`, taking logarithms and dividing by positive
`n` gives

```text
log p_s(n) / n <= log r + log(C + 1) / n.
```

The error tends to zero. T32's full limsup definition therefore yields the
claimed entropy bound while retaining all factors meeting the transient
prefix.

## Named theorems

- `Theory.PiDigits.T33.recurrent_alphabet_entropy_bound`
- `Theory.PiDigits.T33.not_genericV3_implies_factorEntropy_le_logNine`
- `Theory.PiDigits.T33.factorEntropy_gt_logNine_implies_genericV3`
- `Theory.PiDigits.T33.pi_factorEntropy_gt_logNine_implies_exact_V3`
- `Theory.PiDigits.T33.nineDigit_uses_exactly_nine_digits`
- `Theory.PiDigits.T33.nineDigit_everyFiniteWord`
- `Theory.PiDigits.T33.nineDigit_factorComplexity`
- `Theory.PiDigits.T33.nineDigit_factorEntropy`
- `Theory.PiDigits.T33.nineDigit_fails_genericV3`
- `Theory.PiDigits.T33.nineDigit_ne_piDigit`
- `Theory.PiDigits.T33.nineDigit_sharp_counterexample`

## Reproduction and axioms

From the workspace root:

```bash
rm -rf .lake/packages
mkdir -p .lake
ln -sfn /opt/allmath-lean/.lake/packages .lake/packages
lake build TheoryLib
lake env lean removed-workflow-record://todo-theory-pi-digits-t33-1784709615-r0/theory_artifacts/RecurrentAlphabetEntropy.lean
```

The Lean file contains no `sorry`, `admit`, `native_decide`, new axiom, or
unsafe declaration. Its printed principal-theorem audits list only `propext`,
`Classical.choice`, and `Quot.sound`.
