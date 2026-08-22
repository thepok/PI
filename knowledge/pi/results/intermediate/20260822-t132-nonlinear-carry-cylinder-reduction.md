# T132 nonlinear carry-cylinder reduction

Status: `proof sketch`

The bad locus for one T130 adjacent phase pair has an exact four-cylinder
description in terms of the selected nearest-integer carry.  Across several
checkpoints, the coupled phases have an exact finite joint period.  These
facts provide the audited local algebra for the nonlinear route left open by
the T132 linear-gauge no-go; they do not yet prove a canonical return.

V1 remains open.

## One-pair carry cylinders

At one checkpoint write

```text
Q_-=q_(j-1)/48,             Q_+=q_j/48,
C_-=1/4+delta_(n,ell_n-1), C_+=1/4+delta_(n,ell_n),
F_s=C_s+Q_s x_n,
z_s=floor(F_s+1/2),
y_s=F_s-z_s in [-1/2,1/2).
```

Put `a_s=1/4-eps_(j+s)`.  Failure of the strict hit at phase `s` is exactly

```text
y_s in N_s=[-1/2,-a_s] or P_s=[a_s,1/2).
```

Define the integer pair carry and its affine target by

```text
kappa=z_+-10z_-,
D=C_+-10C_-+3x_n.
```

The identity `q_j=10q_(j-1)+144` gives `Q_+-10Q_-=3`, hence

```text
kappa=D-R,                  R=y_+-10y_-.
```

For the four bad sign branches, the exact possible intervals for `R` are

```text
PP: ( a_+-5,          1/2-10a_- ),
PN: [ a_++10a_-,      11/2       ),
NP: ( -11/2,         -a_+-10a_- ],
NN: [ -1/2+10a_-,     5-a_+      ].              (1)
```

The open and closed endpoints in (1) follow from half-open centering and the
strict good inequality.  Thus a pair is bad exactly when, for one of the four
branches, an integer `kappa` satisfies

```text
D-kappa in R_branch.                               (2)
```

Unlike a universal linear elimination, the floor-selected `kappa` records
which discontinuous branch the entry selected.

## Coupling checkpoints without marginalization

At checkpoint `i`, retain

```text
T=M_N/48,
B_i=M_(n_i)/M_N,
U_i=S_(n_i)-B_i S_N,
x_i=e/T+U_i/(B_i T) mod 1.
```

For each phase `r` among all selected pairs, put `A_r=q_r/48`.  As
`e` ranges over `Z/TZ`, that phase has exact period

```text
p_r=T/gcd(A_r,T).
```

Let

```text
P=lcm_r p_r.
```

Because every `p_r` divides `T`, the coupled phase vector has exactly `P`
values, each attained with multiplicity `T/P`.  Therefore a multi-time bad
intersection can be decided exactly by enumerating the `P` coupled vectors
and applying (1)--(2), while retaining every individual `U_i`.  This is not a
density or independent-phase argument.

## Open canonical target

For three consecutive boundary checkpoints, the current target is an exact
restriction on the carry word

```text
(kappa_0,kappa_1,kappa_2)
```

which uses both individual fresh transitions and excludes the canonical
entry by a positive strict margin on a natural unbounded index family.  The
four-cylinder decomposition and joint period make that target reproducible,
but no forbidden canonical word or unbounded family has yet been proved.
