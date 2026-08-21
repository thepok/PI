# T100: universal exact-word charging

Claim label: **machine-checked**. The formal claim is
`DecimalFactorComplexity.T100UniversalCharging.universal_finite_word_charging`
in `T100UniversalCharging.lean`. The file recompiles without `sorry`, `admit`,
new axioms, `native_decide`, unsafe declarations, or compiler-trusting
shortcuts. Its printed axiom set is exactly `propext`, `Classical.choice`, and
`Quot.sound`.

## 1. Scope and provenance

The immutable source is the local formulation
`knowledge/pi/statements/pi-lacunary-near-return-sparsity.txt`. The delivered byte-exact
copy is `canonical_statement.txt`, with SHA-256

```text
cbf56699b651aeb69301265763e38da44feb59c6fd955d2280887e8c06c6a2f8
```

There is no original source URL: the canonical file records that the system
formulated the question on 2026-07-22.

T100 proves only an arbitrary finite-word exact-equality sibling, falling
under the canonical file's A10/A13 cautions. It does not prove or assume any
statement about `Real.pi`, the canonical circle-near-return statistic, T56/C7,
C1, or C2.

The T95 note is an unverified proof sketch. It is not imported as a premise.
T100 re-proves its combinatorial argument in Lean. The T98 note is not used.
The checked T83 and T92 modules are imported only for the established
exact-word interfaces and conventions.

## 2. Normalized formal statement

The main theorem quantifies over:

1. `b : Nat` with `2 <= b`;
2. `n : Nat` with `1 <= n`;
3. `wordLength : Nat`;
4. a finite word `x : Fin wordLength -> Fin b`;
5. the legality condition
   `sampleLength b n + n - 1 <= wordLength`.

Here `sampleLength b n = b^(n/2)`, where `/` is natural-number division. Write
this number as `L`. The alphabet is literally `Fin b`, so it has exactly `b`
symbols. The starts are literally `Finset.range L`, hence exactly
`0, ..., L-1`. The last block coordinate is at most `L+n-2`; therefore the
displayed lower bound on `wordLength` is the exact endpoint condition, and
longer words are allowed. `finiteBlock_apply` machine-checks that no legal
block reads the arbitrary post-endpoint extension.

For each occurring length-`n` block label `u`, `occurrenceStarts` is its set of
starts in `range L`. The local statistics are

```text
shortPairsFor  = sum over i in occurrences of
                 #{j in occurrences | j != i and Nat.dist i j < n}

remotePairsFor = sum over i in occurrences of
                 #{j in occurrences | j != i and n <= Nat.dist i j}.
```

`exactShortPairCount` and `exactRemotePairCount` sum these disjoint label
classes. Thus both statistics are ordered and off-diagonal: every orientation
is represented by its first coordinate `i`, and `j != i` removes the
diagonal. No non-overlap restriction occurs. The short range is exactly
`0 < |i-j| < n`; the remote range is exactly `|i-j| >= n`, so lag `n` is
remote. `shortPairsFor_add_remotePairsFor` machine-checks the partition of all
ordered off-diagonal equal-label pairs.

The explicit real constant is

```text
C_b = (25/6) * (4 + 9*b^2*(b+1)/(b-1)^3).
```

It is `chargingConstant b`, depends only on `b`, and is finite because `b >=
2`. The theorem is

```text
2 * S_b <= 3 * R_b + 2 * C_b * L.
```

## 3. Clause-by-clause T95 referee

| T95 literal clause | Lean witness | Referee result |
|---|---|---|
| Every integer base `b >= 2` | `{b : Nat}` and `hb : 2 <= b` | Exact |
| Alphabet of exactly `b` symbols | `Fin b` | Exact |
| Every `n >= 1` | `{n : Nat}` and `hn : 1 <= n` | Exact |
| `k = floor(n/2)` | natural division `n / 2` | Exact |
| `L = b^k` | `sampleLength b n` | Exact |
| Every finite word of length at least `L+n-1` | `x : Fin wordLength -> Fin b` and `LegalWordLength` | Exact |
| Exactly `L` starts | `Finset.range L` | Exact |
| Length-`n` factors | `blockAt ... n i` | Exact |
| Equal block labels only | `occurrenceStarts` filters by block equality | Exact |
| Ordered pairs | outer sum over the first coordinate, then the second | Exact |
| Off-diagonal pairs | predicate `j != i` | Exact |
| Strict short lag `0 < r < n` | `j != i` and `Nat.dist i j < n` | Exact |
| Overlaps retained | no disjointness or `n <= r` condition in the short statistic | Exact |
| Remote lag includes `n` | predicate `n <= Nat.dist i j` | Exact |
| Longer-than-minimum words allowed | legality is a lower bound, not equality | Exact |
| Explicit finite `C_b` depending only on `b` | `chargingConstant b` with the T95 formula | Exact |
| `2*S_b <= 3*R_b + 2*C_b*L` | conclusion of `universal_finite_word_charging` | Exact |

T83's checked decimal `exactShortPairCount` and T92's checked binary short
statistic enumerate positive lags `1 <= r < n` and multiply by two. T100 uses
the equivalent ordered-pair presentation, making both orientations explicit.
T92's checked long statistic starts at positive lag `n`; T100's remote
predicate likewise includes equality at `n`. T100 does not identify exact word
equality with T56's carry-thickened near-return relation.

## 4. Proof structure

1. `overlap_forces_period` proves directly that two equal overlapping copies
   force their positive start gap to be a period.
2. `card_le_one_add_div_of_separated` injects a separated finite set into
   quotient bins, giving the local occupancy bound.
3. `shortPairsFor_le_period_bound` bounds each label's ordered short load.
4. `local_charging_of_short_bound` proves the coefficient-three charging
   inequality by the square `(5*q-3*m)^2`.
5. `periodicBlocks_card_le` injects period-`p` blocks into their first `p`
   symbols, giving at most `b^p` labels.
6. `weighted_period_sum_le` proves the exact geometric majorant using the
   kernel-checked square-weighted geometric series.
7. `sum_periodOccupancyBound_sq_le` sums the period classes and obtains
   `4 + 9*b^2*(b+1)/(b-1)^3` times `L`.
8. `universal_stream_charging` sums local charging. The finite-word theorem is
   its legal-prefix specialization.

## 5. Reproduction

From the repository root, after the prescribed package-cache setup, run:

```sh
lake build TheoryLib
lake env lean removed-workflow-record://todo-theory-pi-lacunary-near-return-sparsity-t100-1786313502-r0/theory_artifacts/T100UniversalCharging.lean
```

The final six `#print axioms` commands report only the allowed axioms.
