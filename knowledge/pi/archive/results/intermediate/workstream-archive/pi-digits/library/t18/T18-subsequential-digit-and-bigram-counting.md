# T18: Subsequential Decimal Digit and Bigram Counting

Status: the finite-alphabet theorem and its conditional pi specialization are
`machine-checked`. The unconditional specialization to pi is a `proof sketch`
because its T14 input is source-pinned and accepted by the program but is not a
Lean theorem.

## Provenance and exact scope

The immutable statement is `knowledge/pi/statements/pi-digits.txt`, SHA-256
`2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825`.
It has no external URL; this exact local, human-authored file is the program's
canonical source.

The source distinguishes three quantifier readings:

- canonical V1 asks whether every finite decimal word occurs contiguously;
- sibling V2 asks whether every infinite stream is a tail;
- sibling V3 asks whether every infinite stream is a subsequence, equivalently
  whether all ten digits occur infinitely often.

T18 proves only that two unspecified distinct digits, and the directed unequal
bigram joining them, have logarithmically many occurrences along an unbounded
set of prefix lengths. This is partial sibling-V3 information. It proves
neither sibling V3 nor canonical V1.

## Accepted T14 input

This note reuses rather than duplicates the accepted artifact
`knowledge_library/t14/irrationality-measure-digit-changes.md`, whose recorded
SHA-256 is
`431945bf7251d6b31eccaee474d21d80df968e5a5c492304455e6cdf3ea423e2`.
That artifact retains and audits the published source:

- V. Kh. Salikhov, *On the irrationality measure of pi*, Russian Mathematical
  Surveys 63:3 (2008), 570-572;
- DOI: <https://doi.org/10.1070/RM2008v063n03ABEH004543>;
- stable record: <https://www.mathnet.ru/eng/rm9175>;
- retained PDF SHA-256:
  `a871a3fd09a7d606c3b0d6402094e2af7777bf007254aec89a36aee2150ab60d`.

T14 defines `d_1,d_2,...` as the floor-based decimal digits of pi and

```text
C_pi(N) = #{i : 1 <= i < N and d_i != d_(i+1)}.
```

Its derived bound is, for every integer `N >= 1`,

```text
C_pi(N) >= c14 log N - C14,                              (T14)
c14 = 1 / log 8,
C14 = 1 - log(delta) / log 8,
delta = min(1, 7/A),
A = 8 log_10(9) - log_10(kappa),
```

where T14 defines `kappa` as an explicitly displayed positive finite minimum.
Thus `c14 > 0`, and all constants are independent of `N`.

Here is the indexing bridge rather than an implicit identification. T14 sets

```text
a_n = floor(10^n pi),
d_n = a_n - 10 a_(n-1)       (n >= 1),
0 <= d_n <= 9.
```

Therefore `a_n = 10 a_(n-1) + d_n`, and reducing this equality modulo 10 gives

```text
a_n mod 10 = d_n.                                      (T14-index-1)
```

T7 defines the value of its zero-based digit `piDigit i` as

```text
floor(pi * 10^(i+1)) mod 10
  = a_(i+1) mod 10
  = d_(i+1),                                            (T14-index-2)
```

where the first equality uses commutativity of real multiplication and the
fact that pi is positive, so T14's integer floor and T7's natural floor agree.
Consequently

```text
piDigit i != piDigit (i+1)
  iff d_(i+1) != d_(i+2).                               (T14-index-3)
```

As `i` ranges over `0 <= i < N-1`, `i+1` ranges over `1 <= i+1 < N`.
Thus Lean's `changeCount(piDigit,N)` is exactly T14's `C_pi(N)`, with both
counts inspecting the `N-1` adjacent pairs wholly contained in the first `N`
digits.

## Normalized counting statements

For a stream `s : Nat -> alpha` over a finite alphabet and a prefix length
`N`, the Lean file defines

```text
changeCount(s,N)
  = #{i : 0 <= i < N-1 and s_i != s_(i+1)},

occurrenceCount(s,a,N)
  = #{i : 0 <= i < N and s_i = a},

directedBigramCount(s,a,b,N)
  = #{i : 0 <= i < N-1 and s_i = a and s_(i+1) = b}.
```

The finite-alphabet theorem uses the exact set of unequal ordered pairs,
`univ.offDiag`. For a decimal alphabet its cardinality is

```text
10 * 10 - 10 = 90.                                      (1)
```

The formal subsequential quantifier is

```text
exists a b, a != b and for every B there exists N >= B such that ... .   (2)
```

It is not the stronger and unsupported assertion

```text
exists a b N1, for every N >= N1, ... .
```

## Lean-checked finite-alphabet argument

Fix a prefix length `N`. Every change position maps to its unequal ordered
pair `(s_i,s_(i+1))`. Finite pigeonhole gives some pair `(a_N,b_N)` with

```text
floor(changeCount(s,N) / #offDiag)
  <= directedBigramCount(s,a_N,b_N,N).                   (3)
```

Choose one such pair for every `N`. There are only finitely many unequal
pairs, so the infinite pigeonhole principle gives one fixed pair `(a,b)` whose
fiber of chosen prefix lengths is infinite. Every infinite subset of the
natural numbers is unbounded, yielding exactly (2).

For each selected prefix, mapping a bigram occurrence at `i` to its left
endpoint `i`, or injectively to its right endpoint `i+1`, gives

```text
directedBigramCount(s,a,b,N) <= occurrenceCount(s,a,N),  (4)
directedBigramCount(s,a,b,N) <= occurrenceCount(s,b,N).  (5)
```

These steps are theorem
`Theory.PiDigits.T18.exists_fixed_pair_on_unbounded_prefixes`.

## Pi specialization, line by line

Apply the formal theorem to `s = Theory.PiDigits.piDigit`. By (1), along an
unbounded set of prefix lengths for one fixed unequal pair `(a,b)`, (3) is

```text
floor(C_pi(N) / 90) <= directedBigramCount(piDigit,a,b,N). (6)
```

Now fix any threshold `B`. Unboundedness lets us choose one such
`N >= max(B,1)`, so T14 applies. Then:

```text
directedBigramCount(piDigit,a,b,N)
  >= floor(C_pi(N) / 90)                                  by (6)
  >  C_pi(N) / 90 - 1                                    floor loss
  >= (c14 log N - C14) / 90 - 1                          by (T14)
  =  (c14 / 90) log N - (C14 / 90 + 1).                 (7)
```

Weakening the strict inequality in (7) to `>=` gives the theorem's displayed
non-strict bound. Define the explicit T18 constants

```text
c18 = c14 / 90 = 1 / (90 log 8) > 0,
C18 = C14 / 90 + 1
    = (1 - log(delta) / log 8) / 90 + 1,
N0  = 1.                                                  (8)
```

Combining (4), (5), and (7), the same selected `N` satisfies

```text
directedBigramCount(piDigit,a,b,N) >= c18 log N - C18,
occurrenceCount(piDigit,a,N)       >= c18 log N - C18,
occurrenceCount(piDigit,b,N)       >= c18 log N - C18.    (9)
```

Consequently the exact conclusion is

```text
exists a b : Fin 10, a != b and
  for every B : Nat, there exists N : Nat, B <= N and
    all three inequalities in (9) hold.
```

The constants and fixed pair are independent of `B` and `N`. The prefix
lengths are unbounded but are not claimed to include every sufficiently large
integer.

## Formal artifact and trust boundary

`FiniteAlphabetSubsequentialCounting.lean` proves:

- `Theory.PiDigits.T18.exists_frequent_unequal_pair`;
- `Theory.PiDigits.T18.exists_fixed_pair_on_unbounded_prefixes`;
- `Theory.PiDigits.T18.pi_fixed_pair_log_lower_bound_of_T14`.

The last theorem takes (T14) as an explicit hypothesis and machine-checks every
step from that hypothesis through (9), including positivity of `c18`. It does
not encode Salikhov's theorem as an axiom. The accompanying `#print axioms`
output reports only `propext`, `Classical.choice`, and `Quot.sound`.

No finite digit computation is used. The result does not establish recurrence
of digits other than `a` and `b`, occurrence of arbitrary finite blocks,
sibling V3, or canonical V1.
