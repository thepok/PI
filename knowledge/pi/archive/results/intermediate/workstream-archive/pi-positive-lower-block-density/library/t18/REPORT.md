# T18 finite calibration report

## Claim status

This artifact is an **experiment**. Every observation about pi below is
heuristic evidence from fixed finite prefixes only. This report makes no proof
or refutation claim about C1. It does not establish that any pi word has
positive lower asymptotic frequency, zero lower asymptotic frequency, or even
another occurrence beyond the tested prefix. C1 remains open.

The canonical source is
`knowledge/pi/statements/pi-positive-lower-block-density.txt`, whose verified SHA-256 is
`11ec455612e8ab182b7f6c71ba1a64c3b5b30beb5f3ded632cb2ecdc50129cc8`.
Canonical C1 quantifies over every nonempty decimal word and an infinite
liminf. This experiment instead quantifies only over the finite ranges fixed
in `ranges.json`.

## Reproduction result

The two independent pi algorithms produced the same 10,003 ASCII digits after
the decimal point and the same SHA-256:

```text
665f10ecc2c415d58347374c8ca3b6d71c4e8021bad53df9ef5ae7c1d6c598ab
```

The first 50 digits also matched the fixed known prefix. The verifier checked
166,650 exhaustive word-count rows, 90 exact block spectra, 990 T15
contamination inequalities, and 231 T14-T16 automaton identities. All checks
passed. Exact file hashes are locked in `expected_results.json`.

## Exact finite signal

The singleton word `1` separates the known zero-liminf T2 sparse-island
control from both known positive-liminf deterministic controls at all three
tested cutoffs. Pi and the seeded iid realization are included for calibration,
without assigning either finite stream an infinite liminf status:

| stream | count at N=1000 | N=3000 | N=10000 |
|---|---:|---:|---:|
| pi | 116 | 309 | 1026 |
| seeded iid realization | 103 | 308 | 980 |
| Champernowne | 177 | 341 | 1858 |
| T4 balanced | 138 | 396 | 1002 |
| T2 sparse-island | 1 | 1 | 1 |

At block scale `L=8`, the number of fully-contained blocks containing `1` was:

| stream | N=1000 | N=3000 | N=10000 |
|---|---:|---:|---:|
| pi | 603/993 | 1699/2993 | 5709/9993 |
| seeded iid realization | 575/993 | 1732/2993 | 5603/9993 |
| Champernowne | 581/993 | 1352/2993 | 6445/9993 |
| T4 balanced | 429/993 | 1255/2993 | 3552/9993 |
| T2 sparse-island | 2/993 | 2/2993 | 2/9993 |

Thus `v=1`, cutoffs `1000..10000`, and scale `L=8` are a concrete finite
regime where occurrence/contamination diagnostics distinguish the accepted T2
zero-liminf control from the accepted T4 positive-liminf control. This is a
finite calibration result, not an implication in either direction for C1.

## Entropy behavior

`block_entropies.csv` records the exact multiplicity spectrum of all
fully-contained blocks. The symbolic column

```text
ln(total) - sum(multiplicity*count*ln(count))/total
```

is determined entirely by exact integers; decimal columns are evaluations of
that expression. The normalized value is `H/(L*ln(10))`.

At `N=10000,L=8`, the normalized values were:

| stream | H/(L ln 10) |
|---|---:|
| pi | 0.499961985926354904815812856800 |
| seeded iid realization | 0.499961985926354904815812856800 |
| Champernowne | 0.499931861839928007868428313731 |
| T4 balanced | 0.329361640944995071210461545521 |
| T2 sparse-island | 0.003215978686107227062529386881 |

Pi and the iid realization tie here because all 9,993 observed length-eight
blocks are distinct. This is finite-sample saturation: the support cannot
exceed the sample size, so it is not evidence that their infinite entropy
rates agree. T4's substantial finite entropy deficit, despite its accepted
positive lower density for every nonempty word, also shows that entropy
deficit alone is not a reliable finite converse to T15.

At `N=10000,L=32`, pi, iid, and Champernowne again have all sampled blocks
distinct and therefore the same finite-sample entropy. The T2 sparse-island
normalized value is `0.002929001591430818424043468440`; T4's is
`0.083783849368602465800725942824`. The high-scale statistic is therefore
strongly sample-limited for the random-looking streams and remains sensitive
to long deterministic zero runs.

## Exhaustive short words

At `N=10000`, every length-one through length-three word occurred in pi, the
seeded iid realization, Champernowne, and T4 balanced. Their least length-three
counts were all `2`. Many length-four words were absent in every stream at
this cutoff: pi had 3,633 absent length-four words and the iid realization had
3,680. These absences are expected finite-prefix phenomena and say nothing
about the infinite liminf in C1.

The T2 prefix had one absent singleton (`9`) and 83 absent length-two words at
`N=10000`, although the accepted T2 construction is disjunctive and eventually
contains every finite word. This directly demonstrates why finite absence
cannot be interpreted as infinite avoidance.

## Automaton and matrix certificates

For every predeclared forbidden word and power, the delivered JSON contains
the complete formal-state T14 matrix and its exact power. An independent KMP
dynamic program supplies the avoidance count. All 231 checks of

```text
e_initial^T M_v^r 1 = forbidden_count_KMP(v,r)
max_s e_s^T M_v^r 1 = e_initial^T M_v^r 1
M_v^r 1 <= max_row_sum(M_v^r) 1
```

passed, including power zero and all unreachable formal states. These are
finite exact-integer identities. They validate the implementation of the
accepted T14-T16 certificates; they do not instantiate T15's conditional
infinite conclusion for pi.

## Interpretation

The tested signatures do detect the sparse-island obstruction through the
specific word `1` at modest cutoffs and block scale eight. They do not provide
a general finite classifier: T4 exhibits entropy deficits despite positive
lower density, and pi/iid entropy values saturate at the finite sample ceiling
for larger blocks. The useful output for subsequent theory is therefore the
specific occurrence/contamination regime, together with the warning that raw
block entropy at `L >= 8` is already sample-limited for `N <= 10000`.

No proof or refutation of C1 is claimed.
