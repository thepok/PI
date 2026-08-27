# First open π-specific rung

Claim status: `conjecture`.

For a positive natural-diagonal node `(q,A)`, let `C_r(q,A)` be the
complete fresh-block predecessor sector and

```text
P_r(q,A)=C_r(q,A)+conj(C_(10-r)(q,A)),  1≤r≤5.
```

The first clean, non-circular target is the uniform local statement

```text
for every q=10^k and every positive node (q,A),
exists r in {1,...,5}:
  Delta_0(q,A) + |P_r(q,A)|/2 > 21/(10q).          (Pair-π)
```

A weaker direct estimate implying
`max_d Xi_d > 21/(10q)-Delta_0` is equally good. The exact sharp deterministic
bound `max_d Xi_d ≥ |P_r|/2` then proves R1.

This uniform theorem is stronger than FMR needs. A weaker pathwise theorem is
legitimate only when its statement jointly defines a recursive selector
`A_(k+1)=A_k+d_k q_k` and proves the R1/R2 invariants inductively. Merely saying
"for every reached node" assumes the missing transport and is circular.

What is missing is an actual-π quantitative lower bound for the literal
target-evaluated paired sector. Formal nonzero Laurent-polynomial structure,
generic transcendence conjectures, unsigned sector energy, or finite replay do
not give the required `O(1/q)` scale. Pair-π alone also does not prove R2;
the same digit must cover `-G_d`.

Research may replace Pair-π with a genuinely shorter aligned theorem that
directly yields FMR. It may not replace it by an equivalent normalization of
`Xi_d`, or assume the unbounded reached path that the transport must construct.
