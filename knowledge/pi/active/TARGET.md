# Exact target V1

Claim status: `conjecture`.

The canonical Lean statement is
[`Theory.PiDigits.V1`](../../../TheoryLib/PiDigits/T7Statements.lean):

```text
∀ s : List (Fin 10), ∃ n : ℕ,
  ∀ i : ℕ, ∀ hi : i < s.length,
    piDigit (n+i) = s.get ⟨i,hi⟩.
```

It asks whether every finite decimal word occurs contiguously in π. Leading
zeros and overlaps are included; the empty word is vacuous. This is weaker
than base-ten normality and remains open.

Do not silently substitute either sibling problem:

- every infinite stream is a tail of π (false by cardinality);
- every infinite stream is a subsequence of π (equivalent to every digit
  occurring infinitely often, also open for π).

The immutable normalized source and ambiguity record is
[`statement/pi-digits.txt`](statement/pi-digits.txt).
