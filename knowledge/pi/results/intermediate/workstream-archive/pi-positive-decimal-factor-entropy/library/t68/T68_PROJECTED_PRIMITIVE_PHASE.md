# T68 projected primitive-phase recurrent-SCC certificate

Status: `proof sketch` for the generic finite-graph theorem and `experiment`
for the 34-instance census. The generic argument below is inspectable prose,
not a new kernel-checked theorem. The census is exact finite computation. No
part of this package proves the uniform hypothesis, C6, C1, or a new fact
about pi.

## 1. Provenance and canonical scope

The immutable canonical statement is vendored byte-for-byte as
`pi-positive-decimal-factor-entropy.txt`, SHA-256

```text
a70dd741b27595aeb3dfc902b5e201579fed6bae24e2191f58c5ac64a22939e6
```

There is no external source URL: the problem was formulated locally on
2026-07-22. The canonical question asks whether one fixed `eta > 0` satisfies
`p_pi(n) >= 10^(eta*n)` for every sufficiently large `n`. T68 does not address
that assertion directly. It studies a finite-graph sibling certificate in the
conditional times-16 route to C6.

The imported sources and their hashes are:

| File | SHA-256 | Role |
|---|---|---|
| `T46T46LiveSCC.lean` | `9e35511d20b9997e7fd98eaf54bfb3eb3b2e53f42b720d962b671b128bf61ec8` | finite graph, reachability, liveness, SCC and infinite-language conventions |
| `T48EndpointCarryKMP.lean` | `cbe1652c833fb21ae2618aedbc3040a2f29a7db5b310a9f3873536c888c4b211` | exact endpoint-complete carry/KMP graph and coordinate-zero evaluation |
| `T65RationalCoreCertificate.lean` | `6ee5b2a7e35405340fc82e4232582c743b820b89b9c5c73a9598e485b48bcba8` | eventual-periodic decimal rationality and conditional C6 constants |
| `t52_experiment.py` | `5b5d790f623b2e51fa9b6babf48c483bc4e633afafdf1047aaa84e468054e0a0` | exact-integer executable T48 graph convention |
| `t66_instance_table.csv` | `ed3529167b13d291161a9eae1ff38f6125f992ebb6baf2fc734920b9b1b70fe1` | pins T66's 34 completed and 10 capped rows |

The three Lean sources are byte-exact copies of previously kernel-checked
artifacts. Their inclusion makes convention drift inspectable; T68 claims no
new Lean theorem.

## 2. Normalized task and ambiguities

The graph statement uses the following quantifiers.

1. A separate primitive word and phase map may be used for each reachable,
   live, cyclic SCC. No common period across distinct SCCs is required.
2. A closed walk is nonempty. Empty walks have no primitive output word.
3. "Common primitive root" means one common *circular* primitive word. At a
   vertex of phase `a`, the based primitive root is the rotation beginning at
   `a`; roots at different phases need not be literally equal as lists.
4. Phase compatibility is checked on every valid edge whose two endpoints are
   in the SCC. Hidden carry/KMP states and branching targets may differ.
5. Edges leaving an SCC are not constrained by that SCC's certificate. An
   infinite walk traverses only finitely many such edges before its final SCC.
6. "Every accepted output" means only the coordinate-zero digit stream. It
   does not assert eventual periodicity of the full T48 label stream or hidden
   carry states.
7. The finite census reclassifies exactly T66's 34 `completed` rows. Its ten
   `resource_frontier` rows receive no T68 classification.

These choices are essential. Merely asking that every closed walk be periodic,
without a compatible phase shared by intersecting walks, permits arbitrary
concatenations and does not force one periodic output.

## 3. Exact T48 projection and evaluation

For a nonempty decimal word `w` and inclusive depth `R`, T48 uses:

```text
RawState = ((R+1) proper-prefix KMP states, R carries),
carry_j in {-1,0,...,16},
16*d_j + c'_j = d_(j+1) + 10*c_j.
```

The graph has a synthetic root. A root edge has label
`Label.initial(carry,digits)` and every later edge has label
`Label.next(digits)`, where `digits : Fin(R+1) -> Fin 10`. A transition is
discarded if any KMP coordinate completes `w`. Distinct full labels remain
distinct graph edges.

For either label kind, T48 defines `Label.digits` by forgetting only the label
constructor and retaining the complete digit column. The T68 projection is
therefore exactly

```text
rho(e) = e.label.digits(0) in {0,...,9}.
```

T48's `graphEvaluation` is the endpoint-inclusive circle value

```text
circleValue(n |-> rho(e_n)).
```

This includes both decimal endpoint conventions already handled by T48. The
synthetic root has no incoming edge and hence is not in a cyclic SCC; initial
carry data never appears in a recurrent closed walk, although the first output
digit is still projected by the same coordinate-zero rule.

## 4. Primitive words, rotations and phase

Let `A` be a finite output alphabet. For a nonempty finite word
`P = P[0]...P[p-1]`, define:

```text
rot_a(P)[j] = P[(a+j) mod p].
```

`P` is **primitive** if there are no word `Q` and integer `k >= 2` with
`P = Q^k`. Equivalently, no proper positive divisor `q` of `p` satisfies
`P[i] = P[i mod q]` for every `0 <= i < p`. Here and in the checker, "period"
means this divisor/power period, not the unrestricted finite-string period.

For a finite edge walk `W = e_0...e_(ell-1)`, its projected word is

```text
rho(W) = rho(e_0)...rho(e_(ell-1)).
```

Let `C` be one reachable-live cyclic SCC. A **local projected primitive-phase
certificate** for `C` consists of:

```text
p >= 1,
a primitive P in A^p,
phi : C -> Z/pZ,
```

such that every internal valid edge `e : u -> v` satisfies

```text
rho(e) = P[phi(u)],                 (output compatibility)
phi(v) = phi(u) + 1 mod p.          (phase compatibility)
```

Branching is allowed: two edges may have the same source phase and different
hidden targets, provided they emit the same projected symbol and both targets
have the next phase.

The replay includes a three-state probe with phases `0,1,1`, two edges from
the phase-zero state to the two distinct phase-one states, and return edges to
phase zero. Both outgoing branches emit `0` and both return edges emit `1`.
The checker accepts primitive word `01` and period two, demonstrating that the
criterion does not reinstate hidden-state or internal-edge uniqueness. The
probe fails T65's `SimpleDirectedCycleSCC` condition at the phase-zero state,
which has two distinct internal edges. Thus the displayed probe is a
proof-sketch strict-separation witness between T68 and T65's relaxed criterion
on finite labeled graphs.

The **T68 projected recurrent-SCC criterion** requires such a certificate for
every reachable-live cyclic SCC.

## 5. Closed-walk formulation and equivalence

The local condition has the requested closed-walk meaning. If `W` is a
nonempty closed walk of length `ell` based at `u`, repeated phase advancement
gives

```text
phi(u) = phi(u) + ell mod p,
```

so `p` divides `ell`. Repeated output compatibility then gives

```text
rho(W) = rot_(phi(u))(P)^(ell/p).                 (1)
```

Thus every coordinate-zero closed-walk word has the same circular primitive
root `P`, with its literal rotation fixed by the base vertex's phase.

Conversely, suppose `p`, primitive `P`, and `phi` satisfy phase advancement on
every internal edge, and every nonempty closed walk based at `u` satisfies
(1). Take any internal edge `e : u -> v`. Strong connectivity supplies a path
`Q` from `v` back to `u`, so `eQ` is a nonempty closed walk at `u`. Its first
projected symbol is both `rho(e)` and the first symbol of `rot_(phi(u))(P)`.
Hence `rho(e) = P[phi(u)]`. Therefore the closed-walk condition plus compatible
phase is equivalent to the finite local edge test.

This equivalence also explains why comparing unbased primitive roots without
phase is insufficient: rotations and connectors between branch points must
agree.

## 6. Generic eventual-periodicity proof

**Claim (`proof sketch`).** If a finite labeled graph satisfies the T68
projected recurrent-SCC criterion, the projected output of every infinite walk
from its distinguished start is eventually periodic.

**Proof.** Let `e_0,e_1,...` be an infinite accepted edge walk. Collapse the
finite graph to its SCC condensation graph. This condensation is a finite
directed acyclic graph. Whenever the walk leaves an SCC it moves strictly
forward in that DAG and can never return. It therefore crosses only finitely
many SCC boundaries. Choose `N` after its final boundary and let `C` be the SCC
containing every source and target from that point onward.

The finite prefix makes `C` reachable. The infinite tail makes it live. Some
state occurs at least twice in the tail, and the segment between two
occurrences is a nonempty closed walk, so `C` is cyclic. Let `(p,P,phi)` be its
certificate.

Induction on `n` using phase compatibility gives

```text
phi(src(e_(N+n))) = phi(src(e_N)) + n mod p.
```

Output compatibility consequently gives

```text
rho(e_(N+n)) = P[(phi(src(e_N))+n) mod p]
             = rho(e_(N+n+p)).
```

Thus the projected stream is periodic from `N` with positive period `p`.
The argument concludes periodicity only for the projection; hidden paths may
continue branching.
QED.

## 7. Decidable checker and complete finite witnesses

The checker in `t68_projection.py` is a finite decision procedure for the
criterion.

For each reachable-live cyclic SCC `C` it chooses a nonempty anchor closed walk
`A` based at the least state ID. Any certificate period `p` must divide
`|A|`, by phase closure. Hence only the positive divisors of `|A|` need be
tested; this is a complete candidate list, not a search cutoff.

For each candidate `p` the checker sets the anchor vertex phase to zero and
propagates

```text
phi(dst) = phi(src)+1 mod p
```

over all internal edges. Strong connectivity reaches every state, and any
certificate can be rotated so that this normalization holds. The propagation
has three possible outcomes:

1. Two internal paths from the anchor reach one state with different lengths
   modulo `p`. Their edge-ID paths are a `phase_advance_conflict` witness.
2. Propagation succeeds but two internal edges whose sources have one forced
   phase emit different coordinate-zero digits. The two source paths, edges,
   phases and digits are a `projected_digit_conflict` witness.
3. Every phase has one forced digit but the resulting length-`p` word has a
   proper period. The forced word and its proper primitive root are a
   `nonprimitive_forced_word` witness.

If none occurs, the forced word, state phases, and a hash of every checked
internal projected edge form a pass certificate. Completeness follows because
the period divides the anchor length, phase normalization recovers the unique
forced phases, and output compatibility recovers the unique candidate word.

For a failed SCC, `results.json` records the anchor and one replay-validated
rejection for every divisor of its length. This complete finite table is the
`experiment` witness for classifying that finite SCC as having no projected
primitive-phase certificate. It is not an extrapolation to other words or
depths.

## 8. Replayed T66 classification

The checker reads the byte-exact T66 instance table solely to select rows and
to compare graph counts. It rebuilds every completed graph from the exact T48
integer transition rule, validates every KMP/carry edge, recomputes liveness
and SCCs, and applies the new criterion independently of T66's old T65
verdicts.

| Cohort | Completed replayed | T68 pass | T68 failure | Left unclassified |
|---|---:|---:|---:|---:|
| T52 completed baseline | 16 | 0 | 16 | 0 |
| T66 deterministic extension | 18 | 0 | 18 | 10 |

All 34 completed instances have a projected phase-incompatibility witness.
For example, instance 0 (`w = 0`, `R = 0`) has one recurrent raw state. Its
anchor loop has length one, so the only possible period is `p = 1`, but
internal loops emit both coordinate-zero digits `1` and `2` (among others).
The checker records the two edge IDs, equal forced phase, and unequal digits.

This finite result shows that T66's observed internal branching remains
visible after coordinate-zero projection in these 34 cases. It does not show
that every T48 instance fails, that any one word fails at every depth, or that
no uniform projected certificate exists.

## 9. Conditional rational-core and C6 consequences

Fix a nonempty word `w` and depth `R`. If the T48 graph
`carryKMPGraph w hw R` satisfies the T68 criterion, the generic argument makes
the coordinate-zero digits of every accepted path eventually periodic.
T65's kernel-checked theorem
`eventuallyPeriodic_decimal_evaluation_rational` then makes their
endpoint-inclusive real and circle evaluations rational. T48's kernel-checked
`graphEvaluation_image_eq_core` identifies those evaluations with
`Core w R`. Therefore, conditional on the T68 criterion at `(w,R)`, every
point of that fixed core is a rational circle point.

Define the still-unproved uniform hypothesis:

```text
there exist real L,C with L >= 0 such that
for every nonempty decimal word w there exists r in Nat with
  r <= L*|w|+C
and the T48 graph at (w,r) satisfies the T68 criterion.
```

Conditional on the generic proof sketch in Section 6 being correct, this
hypothesis lets the preceding rational-core conclusion replace the T65
relaxed-SCC rational-core step. The remainder of T65's kernel-checked
finite-word maximum, core antitonicity, endpoint-safe avoiding-word separation,
and irrationality argument is unchanged. Under both stated conditions it
yields literal C6 with

```text
A = (L+1)/log(10),
B = 2*L+C,
epsilon_0 = 1/2.
```

No witness for this uniform hypothesis is supplied. The 34 failures and any
future bounded passes are finite `experiment` evidence only and never prove or
disprove the uniform hypothesis or C6. This package states no C1 consequence.

## 10. Artifact-only replay

From a directory containing only the delivered files, run:

```sh
sh ./verify.sh
```

The command uses only Python's standard library, regenerates `results.json`
and `instance_table.csv` in a temporary directory, checks byte equality, and
validates every displayed phase-conflict path and projected digit conflict.
There is no network access, random seed, repository path, or inference from
the ten capped rows.
