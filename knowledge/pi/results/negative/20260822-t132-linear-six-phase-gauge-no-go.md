# T132 linear six-phase gauge no-go

Status: `proof sketch`

Any universal linear relation among several T130 pair phases which eliminates
the arbitrary entry coordinate also eliminates the explicit canonical base
selector `S_N`.  Consequently a primitive linear six-phase resultant cannot
simultaneously be entry-free and retain `S_N`; a canonical separator must use
nonlinear inequalities, selected carries/signs, or other numerator structure.

V1 remains open.

## Exact normalization

Fix a base `N`, put `T=M_N/48`, and retain each checkpoint `n_i` separately:

```text
B_i=M_(n_i)/M_N,
U_i=S_(n_i)-B_i S_N,
x=e/T,
t_i=U_i/(B_i T).
```

Here `e in Z/TZ` is an arbitrary compatible entry.  At checkpoint `i`, for
`s in {-1,0}`, put

```text
j_i=J_(n_i),
Q_i^s=q_(j_i+s)/48,
C_i^s=1/4+delta_(n_i,ell_(n_i)+s),
Y_i^s=C_i^s+Q_i^s(x+t_i).
```

Choose the half-open centered remainder and nearest integer by

```text
r_i^s=center_1(Y_i^s) in [-1/2,1/2),
m_i^s=floor(Y_i^s+1/2),
Y_i^s=r_i^s+m_i^s.
```

All identities below are exact.  The strict hit/bad inequalities are not
used, so no boundary convention is lost.

## Pair normalization

Since `q_j=10q_(j-1)+144`,

```text
Q_i^0-10Q_i^(-1)=3.
```

Therefore

```text
H_i
=(r_i^0+m_i^0-C_i^0)
 -10(r_i^(-1)+m_i^(-1)-C_i^(-1))
=3(x+t_i).                                        (1)
```

Subtracting two checkpoint equations eliminates the common entry:

```text
H_i-H_h=3(t_i-t_h).                               (2)
```

Equation (2) can retain the individual fresh-offset differences, but it no
longer contains the canonical base prefix separately.

## General linear-gauge obstruction

Every linear combination of raw checkpoint phases has the form

```text
sum_a c_a(Y_a-C_a)
=x sum_a c_a Q_a + sum_a c_a Q_a t_a.             (3)
```

A universal relation independent of the arbitrary entry must satisfy

```text
sum_a c_a Q_a=0.                                  (4)
```

For the canonical block,

```text
t_i
=U_i/(B_i T)
=48(S_(n_i)/M_(n_i)-S_N/M_N).
```

The coefficient of the explicit base term `S_N/M_N` in the second sum of
(3) is `-48 sum_a c_a Q_a`, so (4) cancels it as well.  Dividing the integer
coefficient vector by its gcd does not change this conclusion.  Conversely,
a combination with nonzero `sum c_a Q_a` retains the full entry coordinate;
it is an affine reconstruction such as (1), not an entry-free compatibility
relation capable of separating the canonical lift from arbitrary lifts.

## Consequence and scope

This is a scoped `STOP` for the proposed linear primitive six-phase route:
no universal linear elimination can both remove the arbitrary entry and keep
explicit `S_N` dependence.  It also explains why adjacent normalized pair
relations preserve fresh differences while losing the base selector.

The obstruction does **not** address intersections of the six strict arcs,
nearest-integer sign or order restrictions, nonlinear carry identities, or
coefficient arguments which use the selected canonical entry rather than
eliminate it.  Those multi-time canonical routes remain open.
