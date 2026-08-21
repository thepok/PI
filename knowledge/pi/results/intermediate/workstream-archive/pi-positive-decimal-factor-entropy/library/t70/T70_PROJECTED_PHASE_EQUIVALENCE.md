# T70: projected primitive-phase equivalence on one SCC

Status: `proof sketch`. This note gives a complete informal proof of the
finite-graph equivalence requested by T70. It is not machine-checked and makes
no claim about the canonical positive-entropy question, C6, or pi.

## 1. Provenance and scope

The immutable canonical statement is
`knowledge/pi/statements/pi-positive-decimal-factor-entropy.txt`, SHA-256

```text
a70dd741b27595aeb3dfc902b5e201579fed6bae24e2191f58c5ac64a22939e6
```

It was formulated locally on 2026-07-22 and has no external source URL. The
canonical question asks whether the decimal factor entropy of pi is positive.
T70 addresses only a finite-graph sibling statement arising in a conditional
route toward C6.

Only the following kernel-checked conventions are used.

1. T46 defines a finite right-resolving graph `G`, valid edges, finite walks
   `G.IsWalk`, infinite walks `G.IsInfiniteWalk`, reachability
   `G.Reachable`, liveness `G.Live`, cyclicity `G.Cyclic`, and
   `G.SameSCC`.
2. For T48's graph `carryKMPGraph w hw R`, one edge emits one label and the
   coordinate-zero projection is exactly

   ```text
   rho(e) = (e.label.digits)(0) in Fin 10.
   ```

3. Eventual periodicity has T65's explicit meaning: a stream `x` is
   eventually periodic if there are integers `N >= 0` and `t >= 1` such that
   `x(n+t) = x(n)` for every `n >= N`.

The T68 note is used only to identify the predicate under investigation. Its
generic proof sketch and its finite census are not premises here.

## 2. Exact normalized statement

Let `G` be a T46 graph, let `A` be an alphabet, and let
`rho : G.Edge -> A` assign exactly one output symbol to each edge. Fix a state
`q` satisfying

```text
G.Reachable q,  G.Live q,  G.Cyclic q.
```

Write

```text
C = {v : G.State | G.SameSCC q v}.
```

An **internal edge** is a valid edge `e` with `e.src in C` and `e.dst in C`.
An **internal right-infinite walk from v in C** is a function
`z : Nat -> G.Edge` such that `G.IsInfiniteWalk v z` and every `z(n)` is
internal. Its projected output is `x(n) = rho(z(n))`.

A **projected primitive-phase certificate** on `C` consists of:

```text
p >= 1,
a primitive word P = P[0]...P[p-1] in A^p,
a map phi : C -> Z/pZ,
```

such that every internal edge `e : u -> v` satisfies

```text
rho(e) = P[phi(u)],
phi(v) = phi(u) + 1 mod p.                           (PP)
```

Here a nonempty word is primitive if it is not `Q^k` for a word `Q` and an
integer `k >= 2`. The value `P[a]` always uses the representative modulo `p`.

### Theorem T70

Under the displayed hypotheses, the following are equivalent.

1. `C` has a projected primitive-phase certificate.
2. For every `v in C` and every internal right-infinite walk `z` from `v`,
   the stream `n |-> rho(z(n))` is eventually periodic.

The quantifier in (2) is over every starting vertex and every infinite hidden
walk that stays in `C`; it is not restricted to walks from `G.start`, to one
chosen hidden path, or to bounded prefixes.

## 3. Preliminary SCC observation

Every finite walk whose initial and final vertices are in `C` is automatically
internal. Indeed, suppose a walk starts at `u in C`, ends at `v in C`, and
visits a vertex `s`. The prefix and membership of `u` give `q -> u -> s`.
The suffix and membership of `v` give `s -> v -> q`. Hence
`G.SameSCC q s`. Applying this to each edge shows that every vertex and edge
of the walk lies in `C`.

In particular, every closed walk based at a vertex of `C`, and every connector
between two vertices of `C`, is internal. This observation will justify all
infinite concatenations below.

## 4. Finite-word lemmas

For a nonempty finite word `U`, let `U^omega` denote the right-infinite purely
periodic word

```text
U^omega(i) = U[i mod |U|].
```

Call nonempty words `U,V` **compatible at a base vertex** when
`U^omega = V^omega`. This is literal equality from index zero, not equality up
to a rotation.

### Lemma 4.1: common primitive root

For nonempty finite words `U,V`, the following are equivalent.

1. `U^omega = V^omega`.
2. There is a primitive nonempty word `P` and positive integers `a,b` such
   that `U = P^a` and `V = P^b`.

#### Proof

The second condition immediately implies the first. Conversely, write the
common infinite word as `S`. Both `m = |U|` and `n = |V|` are positive periods
of `S`. Let `p` be its least positive period; such a period exists because
`m` is one.

The least period divides every positive period `d` of `S`. Indeed, write
`d = ap+r` with `0 <= r < p`. For every `i >= 0`, periodicity gives

```text
S(i+r) = S(i+r+ap) = S(i+d) = S(i).
```

Thus a positive `r` would be a smaller positive period, so `r=0`. Therefore
`p` divides both `m` and `n`.

Let `P` be the first `p` symbols of `S`. Since `S` has period `p`, its first
`m` and `n` symbols give `U=P^(m/p)` and `V=P^(n/p)`. If `P=Q^k` with
`k>=2`, then `|Q|<p` would be a positive period of `S`, contradicting the
choice of `p`. Hence `P` is primitive. QED.

### Lemma 4.2: explicit incompatible-loop witness

Let `E` and `F` be nonempty closed edge walks based at the same vertex, with
projected words `U=rho(E)` and `V=rho(F)`. If
`U^omega != V^omega`, then the valid right-infinite edge walk

```text
Z = E^(1!) F^(1!) E^(2!) F^(2!) E^(3!) F^(3!) ...   (1)
```

has non-eventually-periodic projected output.

#### Proof

All blocks begin and end at the common base vertex, so (1) is a coherent
right-infinite walk. Suppose its output `x` were periodic from index `N` with
positive period `t`.

Let `a_k` be the output position where the block `E^(k!)` starts and let

```text
b_k = a_k + k! |U|
```

be the start of the following `F^(k!)` block. Choose `k` large enough that:

```text
a_k >= N,
t divides k!,
k! |U| >= L,
k! |V| >= L,
```

where `L = lcm(|U|,|V|)`. Such a `k` exists because `a_k` tends to infinity,
every positive integer `t` divides `k!` for `k>=t`, and factorials are
unbounded.

The difference `b_k-a_k = k!|U|` is a multiple of `t`. Iterating the alleged
period relation therefore gives

```text
x(a_k+j) = x(b_k+j)             for 0 <= j < L.     (2)
```

The left side of (2) is the length-`L` prefix of `U^omega`; the right side is
the length-`L` prefix of `V^omega`. Since `L` is a multiple of both word
lengths, both infinite words have period `L`. Equality of their first `L`
symbols therefore implies `U^omega=V^omega`, a contradiction. QED.

This is the required explicit semantic witness. It is one infinite walk, not
a cardinality argument or a bounded-prefix sweep.

## 5. Certificate implies every output is periodic

Assume a certificate `(p,P,phi)` satisfying (PP). Let `z` be any internal
right-infinite walk from any `v in C`. T46 coherence gives

```text
(z(n)).dst = (z(n+1)).src.
```

Induction on `n`, using phase advancement on each internal edge, gives

```text
phi((z(n)).src) = phi(v) + n mod p.                 (3)
```

Output compatibility and (3) then give

```text
rho(z(n)) = P[phi(v)+n mod p]
          = rho(z(n+p))                             (4)
```

for every `n>=0`. Thus every projected output is periodic from its first
symbol, with positive period `p`. This is stronger than eventual periodicity
and proves `(1) -> (2)` with all starting vertices and hidden branches still
quantified.

## 6. Every output periodic implies a certificate

Assume condition (2): every internal right-infinite walk from every vertex of
`C` has eventually periodic projected output.

### Step 6.1: compatibility of all loops at one base

T46's hypothesis `G.Cyclic q` supplies a nonempty closed edge walk `E0` based
at `q`. Let `U0=rho(E0)`. It is nonempty because one edge emits one symbol.

Let `E` be any other nonempty closed walk based at `q`, and put `U=rho(E)`.
If `U0^omega != U^omega`, Lemma 4.2 constructs the explicit internal infinite
walk

```text
E0^(1!) E^(1!) E0^(2!) E^(2!) ...
```

from `q` with non-eventually-periodic output, contradicting (2). Therefore

```text
U^omega = U0^omega                               (5)
```

for every nonempty based closed walk `E` at `q`.

Choose `p` to be the least positive period of `U0^omega`, and let `P` be its
first `p` symbols. The proof of Lemma 4.1 shows that `P` is primitive and that
every nonempty word whose periodic extension equals `U0^omega` is a positive
power of this same, canonically chosen `P`: its length is a period, the
least-period division argument makes `p` divide that length, and its symbols
are the corresponding prefix of the `p`-periodic word. Hence (5) shows that
the projected word of every nonempty closed walk at `q` is `P^k` for some
`k>=1`. Since one edge emits one symbol, output length equals edge length.
Consequently,

```text
p divides |E|                                      (6)
```

for every nonempty closed edge walk `E` based at `q`.

### Step 6.2: construction and well-definedness of vertex phases

For each `v in C`, strong connectivity supplies a finite path `A:q->v`.
Define

```text
phi(v) = |A| mod p.                                (7)
```

This does not depend on the chosen path. To prove it, let `A,A':q->v` be two
paths. Choose one return path `B:v->q`, and retain the fixed nonempty loop
`E0:q->q`. Both concatenations

```text
A B E0,       A' B E0
```

are nonempty closed walks at `q`. By (6), both lengths are divisible by `p`.
Subtracting the common integer `|B|+|E0|` gives

```text
|A| = |A'| mod p.
```

Thus (7) defines a genuine phase on every vertex of `C`, including `q` and
the possibility of an empty path. In particular `phi(q)=0`.

### Step 6.3: phase advancement and edge output

Let `e:u->v` be any internal edge. Choose a path `A:q->u`. Then `Ae` is a
path from `q` to `v`, so path-independence immediately gives

```text
phi(v) = |A|+1 = phi(u)+1 mod p.                   (8)
```

Choose a return path `B:v->q`. The concatenation `AeB` is a nonempty closed
walk at `q`; by Step 6.1 its projected word is a positive power of `P`. The
symbol emitted by `e` occurs at zero-based position `|A|` in that word.
Therefore

```text
rho(e) = P[|A| mod p] = P[phi(u)].                 (9)
```

Equations (8) and (9) are exactly (PP). They hold for every internal edge,
including parallel hidden branches. This constructs the required certificate
and proves `(2) -> (1)`.

## 7. Complete closed-walk interpretation

The preceding construction also proves the common-circular-root formulation,
rather than merely substituting an unproved local criterion.

Fix `v in C`, a path `A:q->v`, a return path `B:v->q`, and a nonempty closed
walk `W:v->v`. The two nonempty loops

```text
A B E0,       A W B E0
```

at `q` have lengths divisible by `p`. Their length difference is `|W|`, so

```text
p divides |W|.                                    (10)
```

The loop `AWB` at `q` has projected word `P^k`. The subword contributed by
`W` starts at position `|A|`, whose residue is `phi(v)`. Combining this with
(10) gives the exact formula

```text
rho(W) = rot_(phi(v))(P)^(|W|/p).                 (11)
```

Thus every nonempty closed walk at `v` has the same circular primitive root,
and its literal rotation is fixed by the well-defined vertex phase.

For completeness, the closed-walk formulation also implies the edge-output
part of (PP), provided its stated compatible phase map already advances by one
on every internal edge, as in T68's predicate. Take an internal edge
`e:u->v` and a return path `Q:v->u`, supplied by strong connectivity. Then
`eQ` is a nonempty closed walk at `u`. Its first projected symbol is both
`rho(e)` and the first symbol of `rot_(phi(u))(P)`, so
`rho(e)=P[phi(u)]`. In the other direction, (PP) gives (10) by summing phase
increments around `W`, and gives (11) by reading the emitted symbol at every
step. Hence the edge predicate and the based closed-walk predicate, including
the explicitly required compatible phase advancement, agree with all closed
walks quantified.

## 8. T48 specialization and exact limits

Take `G=carryKMPGraph w hw R` from T48 and

```text
rho(e) = (e.label.digits)(0).
```

For every state `q` that is reachable, live, and cyclic, Theorem T70 applies
to its full T46 SCC. Therefore T68's projected primitive-root and compatible
vertex-phase predicate on that one SCC holds if and only if every
right-infinite T48 edge walk staying in that SCC has eventually periodic
coordinate-zero output.

No statement about all words `w`, all depths `R`, the T66 census, decimal
rationality, C6, C1, or pi follows here. T65's rational-evaluation theorem is
not used. The result is solely the requested finite-graph equivalence for one
reachable live cyclic SCC.

## 9. Ambiguities resolved

1. The SCC is the complete equivalence class `G.SameSCC q`, not a selected
   subgraph or a bounded reachable set.
2. Infinite walks may start at any SCC vertex, and every edge must remain
   internal. Hidden paths may branch indefinitely.
3. Every edge emits exactly one projected symbol. The phase is edge length
   modulo `p`; the theorem would need modification for variable-length or
   empty edge outputs.
4. Closed walks are nonempty. T46 cyclicity excludes the vacuous edgeless
   singleton case and supplies the base loop `E0`.
5. At the chosen base vertex, compatibility is literal equality of periodic
   words. At other vertices, roots are rotations determined by `phi`.
6. No period is required to be common to distinct SCCs.

## 10. Search record

Before constructing the proof, mathlib and the standard word-combinatorics
literature were checked on 2026-08-02.

1. Mathlib's `Mathlib/Data/List/PeriodicityLemma.lean` contains
   `List.HasPeriod.gcd`, the Fine-Wilf periodicity lemma. The inspected source
   has SHA-256
   `aff79c7c665556b6f4bbf053ec86e81a04d8fb39e060eed7005bb112819a5c27`.
   T70 does not use it as a premise because Lemmas 4.1 and 4.2 above are
   elementary and self-contained.
2. N. J. Fine and H. S. Wilf, "Uniqueness Theorems for Periodic Functions,"
   Proceedings of the AMS 16 (1965), 109-114,
   DOI `10.1090/S0002-9939-1965-0174934-9`. The retrieved AMS PDF had SHA-256
   `4ab0417ea85b6b792e2f97a810f418fd07dd53b125341eac707f3d67f758c2d7`.
   This is background only; no external theorem is needed in the proof.

## 11. Conclusion

The equivalence is true. The reverse implication is semantic: any two
incompatible based closed walks explicitly generate the factorial-block
non-eventually-periodic output (1). Universal eventual periodicity therefore
forces closed-walk compatibility; connector lengths then give well-defined
vertex phases, and closing each internal edge proves both required local
conditions. The forward implication reads the phase along an arbitrary
infinite internal walk and gives periodicity from index zero.
