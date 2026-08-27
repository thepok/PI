# T136: three-growth scalar-kernel no-go and comparator census

This note records two separately labelled scoped negative findings. Neither is
a result about eventual decimal hits.

## One-row BAD-kernel obstruction

Status: `proof sketch`

For `k>=4`, put

\[
Q_k=\frac{10^k-16}{48}.
\]

Then `Q_k` is a positive integer and

\[
Q_{k+1}=10Q_k+3.
\]

Moreover `10^k-16` is congruent to `3` modulo `9`, so its 3-adic
valuation is exactly one. Since `48` also has 3-adic valuation one,
`3` does not divide `Q_k`, and therefore

\[
\gcd(Q_k,Q_{k+1})=\gcd(Q_k,3)=1.
\]

Consider finitely many literal registered phase equations on the circle,

\[
Q_i x+\eta_i=z_i+y_i,
\]

where BAD restricts

\[
y_i\in O_i=[-1/2,-d_i]\cup[d_i,1/2),
\qquad d_i=1/4-\varepsilon_i,
\qquad 0<d_i<1/4.
\]

Let `lambda` be one nonzero exact integer entry-eliminating row,

\[
\sum_i\lambda_iQ_i=0.
\]

It yields the scalar necessary relation

\[
\sum_i\lambda_i y_i\equiv
\sum_i\lambda_i\eta_i\pmod1.
\]

This one relation cannot itself obstruct BAD when the `y_i` are otherwise
treated independently. If some `|lambda_i|>=2`, multiplication maps the BAD
arc `O_i` onto the full circle because its circular length is greater than
`1/2`. Otherwise at least two nonzero coefficients are `+1` or `-1`; a single
nonzero coefficient cannot annihilate the positive `Q_i`. Reflection preserves
`O_i`, and the sum of any two such BAD arcs is the full circle because
`d_i+d_j<1/2`. Hence

\[
\sum_i\lambda_iO_i=\mathbb R/\mathbb Z.
\]

The half-open convention introduces no gap: every registered epsilon is
strictly positive, so the relevant arc-length inequalities are strict.

This is only a one-row relaxation no-go. It does **not** show that the full
rank-five kernel image is jointly surjective for one common vector of six
phase residues. It does not cover denominator-aware modular kernels without
additional work, coupled fresh-block constraints, or a multirow Smith/CRT
certificate. Rowwise surjectivity must not be upgraded to simultaneous
surjectivity.

## Last-three-growth comparator diagnostic

Status: `experiment`

For every base `65<=n<=128`, let

\[
L_n=\left\lceil
  (\log_{10}(8/5)+1/100)n
\right\rceil
\]

and choose the last three `r` in `[0,L_n-1]` for which
`Lambda_(n+r+1)>Lambda_(n+r)`. At each of the three successor checkpoints,
intersect both literal BAD phases. Compare:

- the canonical entry; and
- `e_n^*=63T_n/64`, propagated through the same exact BBP increments.

All 64 bases are eligible. The exact membership census is

```text
(canonical outside, comparator outside): 64
(canonical outside, comparator inside):   0
(canonical inside,  comparator outside):  0
(canonical inside,  comparator inside):   0
```

Thus the predeclared finite diagnostic has no base at which its selected
six-BAD cylinder contains the comparator while excluding the canonical entry.
It excludes both entries at every tested base, so this range supplies no
canonical/comparator transversality evidence.

At the first base, the exact replay gives

```text
n=65, L=14
growth r=(10,11,12), checkpoints=(76,77,78)
canonical phase bits=((false,true),(true,true),(true,true))
comparator phase bits=((false,false),(false,true),(true,false))
```

## Exact replay and audit

Run:

```text
python3 workflows/research/pi/t136_three_growth_cylinder_census.py
```

Audited script SHA-256:

```text
4268be4fa91f123c979d7b2621f19583414e91bdaf812c7e4f18f2f2e14b142b
```

The script uses exact `Fraction` and integer arithmetic for every phase and
BAD decision. It certifies each logarithmic horizon candidate by exact power
inequalities, constructs every lcm-growth step exactly, and independently
replays canonical and comparator phases through direct centered identities.
An independent audit also reproduced the full census using recurrence-
propagated integer residues rather than the script's closed normalized forms.

Three corrected-prompt Oxzen memos with raw hashes beginning `47c355f`,
`0c43b93`, and `79fea05` were rejected: each claimed retained computations or
logs that were absent, and none supplied a valid transversality certificate.

## Scope

The `proof sketch` closes only a single scalar entry-eliminating relation with
otherwise independent BAD variables. The `experiment` covers only the finite
declared range and the specified last-three-growth selection. Neither proves
full projection, an unbounded-family result, or a multirow Smith/CRT no-go.
Neither advances T125, `(D)`, or V1.

V1 remains open.
