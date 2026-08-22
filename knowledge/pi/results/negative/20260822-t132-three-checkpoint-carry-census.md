# T132 three-checkpoint carry census

Status: `experiment`

Exact finite arithmetic refutes universal escape at the three consecutive
T129-boundary checkpoints and finds no compact raw or normalized carry-word
language among the surviving canonical windows.  This is finite negative
evidence against the local three-checkpoint carry route, not an eventual
escape theorem or an infinite-memory obstruction.

V1 remains open.

## Frozen census

For every `6<=N<=512` and `c in {0,1,2,3}`, let `H_N` be the least integer
strictly greater than

```text
log_10(6(N+1)^2(8/5)^N)
```

and inspect the physical checkpoints

```text
n_r=N+H_N+c-2+r,  r=0,1,2.
```

At every checkpoint the census uses the exact registered `A_n`, `ell_n`,
`J_n`, `delta`, `epsilon`, half-open centering, and nearest integers.  It
records the pair carry

```text
kappa_r=z_(r,0)-10z_(r,-1)
```

only when both strict sufficient-hit tests fail at all three checkpoints.
The comparator starts from the exact noncanonical entry `63/64` and retains
the base-dependent translation `48(A_(n_r)-A_N)`.

## Exact counts

The canonical census has

```text
88 (N,c) rows,
27 distinct physical consecutive-checkpoint triples,
25 distinct raw carry words.
```

The 27 physical starting indices are

```text
60,61,142,168,169,170,188,207,247,256,285,
335,336,337,386,387,421,449,484,485,510,511,
518,519,520,566,567.
```

The first physical triple `60,61,62` is represented redundantly by

```text
(N,c)=(45,3),(46,2),(47,1),(48,0)
```

and has carry word `(-4,-3,-3)` with all six centered phases negative.  Thus
the claim that every registered three-checkpoint boundary window contains a
strict hit is finitely false.  Other smallest witnesses include:

- a within-pair sign switch at `(46,3)`;
- all-positive signs at `(135,3)`;
- constant carry word `(3,3,3)` at `(136,3)`;
- five consecutive bad base indices `134..138`.

The comparator has `95` base-dependent triple-bad rows and `81` raw carry
words.  There are `92` distinct checkpoint-index triples; three repeat with
different base-dependent comparator phases, so all `95` full phase tuples
are distinct.  The canonical and comparator raw-word sets are disjoint in
this declared window, but that finite fact supports no asymptotic separator.

## Normalized-defect audit

Put

```text
D_r=C_(r,0)-10C_(r,-1)+3x_r,
d_r=kappa_r-floor(D_r+1/2).
```

Among the 27 canonical physical survivors there are

```text
25 defect triples,
16 sign-branch triples,
27 distinct combined (defect,sign)^3 words.
```

Only defect triples `(3,4,-3)` and `(4,3,4)` repeat, each twice, and their
sign words differ.  Hence the cheap bounded normalization produces no
collision at all after signs are retained.  This is strong finite evidence
that the proposed local carry word is labeling individual bad windows rather
than exposing a reusable small state.

## Independent replay

The durable script is
`workflows/research/pi/t132_carry_word_census.py`.  Two independent Fraction
implementations reproduced every aggregate above.  Each replay also checked
all `12,168` canonical phase evaluations directly against
`center_1(q_j A_j)`; the comparator implementation independently expanded
its translated phase and matched all `12,168` evaluations.  The least
retained strict margin is greater than `1/1000` canonically and greater than
`1/100000` for the comparator, so no boundary ambiguity affects the counts.

## Scope and direction

The experiment closes only the current raw/normalized three-checkpoint
pattern-mining proposal.  It does not rule out an eventual three-checkpoint
escape threshold, a specified infinite coefficient family, longer
variable-length cylinders, or a nonlocal arithmetic obstruction.  The next
route must use the complete intermediate fresh-numerator history over a
supercritical variable-length block rather than another bounded carry-word
dictionary.
