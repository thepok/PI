# T134: finite reduced-profile cylinder nonseparation witness

Status: `experiment`

## Result

At base `n=6`, let

\[
\Lambda_m=\operatorname{lcm}_{k\le m}D_k,\qquad
M_m=16^m\Lambda_m,\qquad A_m=S_m/M_m,
\]

and propagate a counterstate on the canonical denominator chain by

\[
S'_{m+1}=16\frac{\Lambda_{m+1}}{\Lambda_m}S'_m
 +\nu_{m+1}\frac{\Lambda_{m+1}}{D_{m+1}}.
\]

The exact choice `S'_6=S_6-570` is noncongruent to `S_6` modulo `M_6`. For
`L_6=ceil((log_10(8/5)+1/100)6)=2`, it has the same nearest-integer carry `z`,
phase sign, and bad/good Boolean as the canonical state at both registered
phases for every physical depth `r=0,1,2`. All six phases are negative and bad,
and every bad margin for both states is greater than `1/100`.

It also has the same numerator-denominator gcd profile as the canonical state
for four consecutive depths. The canonical/counterstate gcd pairs are exactly

```text
(5,5), (40,40), (5,5), (190,190).
```

The exact centered phase residues are different. Thus the witness defeats only
the coarse finite selector consisting of `(gcd,z,sign,bad)`; it does not defeat
a condition retaining the full phase residue or margin.

## Exact replay

Run:

```text
python workflows/research/pi/t134_reduced_profile_witness.py
```

The script uses integer and `Fraction` arithmetic, independently checks the
canonical direct identity `center_1(q_j A_j)` at all six phases, verifies the
half-open phase convention, the four gcd equalities, noncongruence modulo
`M_6`, and strict distance from all boundaries.

## Scope

This is a finite countermodel. It is a scoped negative result for proposed P9
discriminators using only four gcds and the finite `(z,sign,bad)` address. It
does not establish nonseparation for longer or unbounded cylinders, does not
produce another canonical BBP prefix, and has no direct implication for `D`,
eventual return, or V1.

V1 remains open.
