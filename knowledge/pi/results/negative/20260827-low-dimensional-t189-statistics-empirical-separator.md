# Low-dimensional T189 statistics fail empirical adversarial tests

Date: 2026-08-27 UTC

Claim label: `experiment`. This is a bounded empirical separator, not a proof
about all possible pi-specific statistics and not a fixed-pi sign theorem.

## Actual source of the finite positive block

For the current fresh block

```text
q=1000, A=334, d=3, N=10000, H=100000,
Q=10000, B=3334,
```

independent evaluations of the exact T179/T189 closed nonmultiple-frequency
kernel reproduce

```text
Xi_3(N,H) ~= 43.16412945.
```

The signal is extremely local. Of the total, `42.76642287` (99.08 percent)
comes from the 79 orbit states whose next three digits are `334`:

```text
9 states 3334       contribute  +113.25379329,
70 states a334,a!=3 contribute   -70.48737042,
all other states    contribute    +0.39770658.
```

Thus the observed positive block is not explained by a global digit moment,
positive-step frequency, or excess number of target hits. There are exactly
nine `3334` hits, equal to the uniform expectation for 90,000 positions. Their
sub-cell placement, together with the competing predecessor states, carries
the sign.

## Periodic sign reversals

The count statistic

```text
9 * count(3334) - count(a334 with a!=3)
```

is positive for pi but does not determine the kernel sign. The periodic word
`0003334` has positive signed count `+9` and true Xi per period approximately
`-0.02457944`. The periodic word `3334013344607` has count `+8` but Xi
approximately `-2.23356368`: its target state contributes only about `+0.2133`
while a competing `133446...` state contributes about `-2.4274`.

Replacing each suffix by an `L`-digit cell midpoint predicts the actual pi
block as follows:

```text
L=1  -0.0017    L=2  -0.0425    L=3  +0.0641
L=4 +27.1414    L=5 +44.8844    L=6 +42.9285
L=7 +43.1556    true +43.1641.
```

But periodic tails reverse even the refined signs: `0003334` remains negative
while its `L=4,5,6` surrogates are positive; separate examples reverse the
`L=5` and `L=6` predictions. Reliable reconstruction begins only when the
feature resolves enough suffix digits to approximate the original kernel.

Raw hit counts, hit-center quality, maximum subblock drawup, predecessor
counts, low digit moments, simple nonlinear distance features, and index
classes modulo 3 or 5 all likewise fail either circularity or a periodic /
replacement-control test.

## Out-of-sample block and whole-class separators

The same literal `Q=10000`, `B=3334` kernel was evaluated on eighteen
disjoint 10,000-step blocks of the certified pi prefix.  The local signed
count

```text
9 * count(3334) - count(a334 with a!=3)
```

remains correlated with the kernel value but does not preserve the sign or
the robust T189 threshold.  In particular,

```text
[20000,30000):   signed count +3,  Xi ~= -4.080195952
[160000,170000): signed count +19, Xi ~= -9.004425325.
```

The second block contains three target hits.  Their weighted contribution is
only `+4.413438652`, while eight competitors contribute `-12.638981782`.
This is an actual-pi out-of-sample failure, not merely a synthetic control.

There is also a separator for the entire class of additive statistics of at
most four consecutive digits.  Two decimal de Bruijn cycles of order four
have identical cyclic histograms for every word of lengths one through four,
including every `a334` and `3334` count.  Deterministic generator seeds 26 and
10 nevertheless give opposite literal kernel values:

```text
seed 26: Xi ~= -12.7448902381
seed 10: Xi ~= +12.5547823886.
```

Thus no additive statistic determined by length-at-most-four cylinder counts,
digit moments, or transition counts can determine the T189 sign at this
scale.  This does not exclude longer-window, nonlinear, ordering-sensitive,
or full arithmetic-state statistics.

The double-precision replay sources are
`workflows/experiments/t189_pi_block_oos.cpp` and
`workflows/experiments/t189_debruijn_order4_separator.cpp`.  They use the
literal T142 coefficient formula and the existing certified digit file.  The
first reproduces the registered nine-block aggregate
`43.164129457`; the second verifies equality of all two cycle histograms for
lengths one through four before reporting the sign reversal.

## Pi-representation state tests

On 4,096 stratified actual-pi suffixes, a separate held-out test used exact
finite-field states

```text
R_p(n) = 10^(n+4) * bbpPartial(7(n+4)) mod p
```

for three primes above every tested BBP pole denominator. Sine/cosine features
of these residues had largest individual absolute Pearson correlation below
`0.027` with the T179 contribution; joint held-out correlation was negative
and no better than rational, periodic, circular, or replacement controls.

The signs and decimal log-overshoots of the first omitted Machin (`1/5` and
`1/239`) and Chudnovsky terms behaved similarly. Individual correlations were
below `0.027`; joint pointwise and 100-step-block models had no held-out
advantage over controls or the majority baseline.

## Scope

The bounded evidence rejects the tested **low-dimensional** explanations of
the finite positive Xi block. It does not reject a full numerator state, a
high-dimensional carrier coupling, or a genuinely new pi-specific invariant.
It does show that a candidate based only on counts, a few suffix cells,
residue clocks, or special-function remainder clocks should not be promoted
to a lemma ladder. The strongest surviving statistic is the fully weighted
local `a334` contribution itself, which is already close to evaluation of the
original kernel and has no independent pi-specific source.
