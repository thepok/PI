# T139: small-prime obstruction for the translated pair-minor determinant

Status: `proof sketch`

At a selected phase pair write

\[
 Q_-=(10^{J-1}-16)/48,\qquad Q_0=10Q_-+3,
\]

and

\[
 \xi=Q_-z_0-Q_0z_-,\qquad K=\xi_0\xi_3-\xi_1\xi_2.
\]

For every registered depth, `J-1 >= 5`. Since `10^(J-1) = 64 (mod
96)`, `Q_-` is odd. Since `10^(J-1) = 64 (mod 144)`, `Q_- = 1
(mod 3)`. Consequently both `Q_-` and `Q_0` are one modulo 2 and modulo
3. (The mod-96 and mod-144 lifts are essential; one may not divide a
congruence modulo 2 or 3 directly by 48.) Therefore

\[
 \xi_j=z_{j,-1}+z_{j,0}\pmod2,
 \qquad
 \xi_j=z_{j,0}-z_{j,-1}\pmod3. \tag{1}
\]

Thus divisibility of `K` by 2 or 3 is exactly a rank-one condition on the
four *observed carry combinations* in (1). It is not forced by the
coefficient relation `Q_0=10Q_-+3` or by the residues of `Q`: those
coefficient residues are constant and impose no determinant relation. Any
successful subfamily still needs an independent canonical-numerator argument
that forces its carry cells; selecting the cells after observing `z` is
circular.

This gives `STOP` only to:

- unconditional canonical quarter-family claims `2|K` or `3|K`;
- any claimed 2/3 divisor derived solely from the displayed `Q` identities;
- a universal arbitrary-four-checkpoint implication `all BAD => 3|K`;
- a universal P14 contradiction with `Delta=2` or `Delta=3`, because the
  known all-BAD values are nonzero and far larger than either divisor.

It does not close a predeclared coefficient-defined infinite subfamily on
which canonical `S` arithmetic independently forces (1), a restricted parity
theorem, a quarter-specific BAD bound, or divisors containing other factors.

## Exact experiment

Status: `experiment`

On the first 32 eligible quarter bases `n=10..41`, exact canonical values have
the following residues:

```text
K mod 6: {0: 6, 1: 1, 2: 10, 3: 3, 4: 10, 5: 2}
```

In particular the base `n=17` has `K=5 (mod 6)`, falsifying unconditional
divisibility by either 2 or 3. Among the ten chronological four-of-five
subsets of the known all-BAD runs `168..172` and `335..339`, all ten `K` are
nonzero. All five subsets of the first run have residue zero modulo 6. In the
second run, four do, while `(335,336,338,339)` has residue two. Hence literal
all-BAD does not universally imply `3|K`. The ten even examples neither prove
nor falsify an all-BAD parity statement.

Exact replay:

```text
python3 workflows/research/pi/t139_pair_minor_small_prime_audit.py
```

The verifier reuses the exact registered inclusive-BBP phase replay in
`t138_plucker_content_census.py`; it performs no floating-point phase or BAD
decision.

Verifier SHA-256:

```text
730e3147967c439acf964464e70d4cd17de55ade98c5c3b3371a3b80462b551f
```

The translated pair-minor route remains open only beyond these precisely
excluded small-prime arguments. V1 remains open.
