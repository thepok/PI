# Appearance ratio is not a standalone route to T19 or V1

Status: `proof sketch` negative separator. The cited Lean interfaces are
`machine-checked`; this report adds no Lean theorem and makes no claim about
whether pi itself has bounded appearance ratio.

## Exact route and obstruction

For length `m`, let `p_m` be pi's factor complexity and let `L_m` be one plus
the latest first occurrence among its distinct length-`m` factors. Canonical
T26–T28 prove that at least `10^m/16` selected frequencies in
`1, ..., 10^m` have the full-prefix additive gap

```text
p_m / 32 ≤ L_m - |S_{L_m}(h)|.
```

T29 converts a pointwise hypothesis `L_m ≤ C p_m` into

```text
|S_{L_m}(h)| / L_m ≤ 1 - 1/(32C)
```

on that same moving selected set. Even the best possible ratio `C = 1` gives
only `31/32`. T19 instead requires, at each length, one prefix controlling
every nonzero frequency through `2 * 10^m` at a threshold of order `10^-m`.
Thus three gaps remain even if appearance ratio is solved optimally:

1. selected frequencies versus every natural-scale frequency;
2. a fixed relative gap versus a normalized norm tending to zero;
3. a scale-dependent selected set with no cross-scale coherence.

Accordingly, T28–T29 remain useful diagnostics, but bounded appearance ratio
alone is not a continuation from those interfaces to T19 or V1. A route that
also supplies genuinely new complement or all-frequency control is not ruled
out.

## Sharpness of the exposed complement estimate

For `64 ∣ P`, put `63P/64` selected unit phases at `+1` and `P/64` at `-1`.
Their sum is `31P/32`. Put all `N-P` omitted phases at `+1`. The full norm is

```text
N - P/32.
```

At `N = C P`, this exactly attains `1 - 1/(32C)`. This model addresses only
the data exposed to T27/T29; it does not claim to realize T26's separated-cell
geometry or the pi orbit. It shows that algebraic rearrangement of the same
selected-norm plus complement information cannot yield a stronger bound.

## Maximal-language timing separator

For any prescribed sequence `A_m ≥ 1`, a recurrent disjunctive decimal stream
can be constructed with

```text
p_s(m) = p_s^rec(m) = 10^m
```

and maximal factor entropy, while the first occurrence of `9^m` begins only
after `A_m 10^m`. Build nested prefixes stage by stage: insert a sufficiently
long zero pad, then the first `9^m`, then a zero-separated enumeration of all
words of length at most `m`. Earlier stages contain no run `9^m`; every fixed
word reappears in every sufficiently late enumeration. Hence every word
recurs, yet `L_s(m) > A_m p_s(m)`.

This generic separator refutes implications from disjunctivity, maximal
ordinary or recurrent factor complexity, or maximal entropy to bounded first-
appearance ratio. It makes no claim about pi and no claim about the separate
long-lag collision-decay predicate.

## Provenance and direction

- GPTPro deliverable commit:
  `6a414a7f8ada75e493c2ed5faaf2ec720fe43c3b`.
- completion commit: `15112e2`.
- independently reviewed against T19 and T23/T26–T30 on 2026-08-21.

The live pi route remains exact full-numerator/full-denominator BBP phase
representation followed by a numerator-sensitive signed all-frequency or
prescribed-cell estimate. This negative result gives no C1/V1 conclusion.
