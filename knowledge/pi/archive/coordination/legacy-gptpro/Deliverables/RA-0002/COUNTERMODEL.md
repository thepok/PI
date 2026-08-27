# RA-0002 countermodel — appearance ratio does not imply disjunctivity

## Claim being falsified

The generic implication

```text
a uniform bound on
  (least prefix containing all length-m factors) / (number of length-m factors)
implies that every length-m word occurs
```

is false.

This does **not** refute the pi-specific appearance-ratio conjecture. It refutes
using that ratio alone as a generic bridge to V1.

## Countermodel

Let the decimal stream be constant:

```text
s(n) = 0  for every n.
```

For every positive length `m`:

1. The only length-`m` factor is `00...0`.
2. Therefore the factor complexity is
   `p_s(m) = 1`.
3. Its first occurrence starts at position `0`.
4. The least positive prefix containing all canonical first occurrences has
   length `L_s(m) = 1`.
5. Hence
   `L_s(m) <= 1 * p_s(m)` for every `m`.

Thus the strongest possible uniform appearance ratio holds with `C = 1`.

Nevertheless the one-letter word `[1]` never occurs, so the stream is not
disjunctive and its factor entropy is `0`, not `log 10`.

## Consequence for the checked pi route

T29's conditional conclusion—a fixed relative exponential-sum saving on a
moving positive-proportion frequency set—cannot be promoted to V1 merely by
proving a uniform appearance ratio. Any valid additional bridge must use
substantially more information, such as maximal factor coverage, suitable
all-frequency cancellation, or a hypothesis that explicitly excludes this
constant-stream behavior.

## Falsification verdict

- Uniform appearance ratio alone: **falsified as a generic sufficient
  condition**.
- Pi-specific uniform appearance ratio: **open**, but insufficient by itself.
- T29's checked conditional theorem: unaffected.
