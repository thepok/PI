# T134: piecewise address stability and gcd-profile CRT reduction

Status: `proof sketch`

## Piecewise exact address cells

Fix a base `n>=6`, horizon `L`, and canonical normalized entries

\[
x_i=\operatorname{frac}(48A_{n+i}-573/4),\qquad 0\le i\le L.
\]

For an integer numerator offset `t`, propagate using the unchanged fresh BBP
increments. With `B_i=M_(n+i)/M_n`,

\[
S'_{n+i}=S_{n+i}+B_i t,\qquad
x'_i=\operatorname{frac}\!\left(x_i+\frac{48t}{M_n}\right).
\]

For an integer `h`, define the wrap cell

\[
W_{i,h}=\left\{t:\frac{M_n}{48}(h-x_i)\le t
 <\frac{M_n}{48}(h+1-x_i)\right\}.
\]

On this cell, `floor(x_i+48t/M_n)=h`. At phase `a=(i,s)`, with
`j_a=J_(n+i)+s`, the literal uncentered phase therefore shifts by

\[
\Delta_a(t)=\frac{q_{j_a}t}{M_n}-\frac{q_{j_a}}{48}h.
\]

Let `y_a` be the canonical centered remainder and
`d_a=1/4-epsilon_(j_a)`. With zero assigned positive sign, its coarse branch
cell is exactly one of

\[
[-1/2,-d_a],\quad [d_a,1/2),\quad (-d_a,0),\quad [0,d_a),
\]

for negative-bad, positive-bad, negative-good, and positive-good respectively.
Call that endpoint-typed interval `I_a`.

The integer offsets preserving the same absolute nearest integer `z`, sign,
and bad/good Boolean at every tested phase are exactly the union over wrap
vectors `(h_0,...,h_L)` of

\[
\mathbb Z\cap\bigcap_i W_{i,h_i}\cap
\bigcap_{a=(i,s)}\frac{M_n}{q_{j_a}}
\left(I_a-y_a+\frac{q_{j_a}}{48}h_i\right).
\]

Each nonempty summand is a rational interval with inherited open/closed
endpoints. For address preservation, take `t` modulo `T_n=M_n/48`, for example
`0<=t<T_n`; then only finitely many wrap vectors occur. In the stated `n>=6`
range, every tested `q_j/48` is integral. The simpler single interval obtained
by omitting the wrap term is therefore valid for centered sign/bad alone, or
when `h_i=0` is proved at every physical depth; it is not a general formula for
preserving the absolute `z` values. No periodicity of the gcd sieve is asserted.

The recorded `n=6,t=-570` T134 witness is in one no-wrap cell at depths 6, 7,
and 8, so this correction does not change that exact `experiment`.

## Exact gcd-profile sieve

At selected physical depth `i`, put

\[
g_i=\gcd(S_{n+i},M_{n+i}),\quad
s_i=S_{n+i}/g_i,\quad d_i=M_{n+i}/g_i.
\]

Then

\[
\gcd(S_{n+i}+B_i t,M_{n+i})=g_i
\]

is equivalent to `g_i | B_i t` and

\[
\gcd(s_i+B_i t/g_i,d_i)=1.
\]

For several selected depths, define

\[
A=\operatorname{lcm}_i\frac{g_i}{\gcd(g_i,B_i)},\qquad
t=Au,\qquad \beta_i=B_iA/g_i.
\]

All `beta_i` are integers, and the remaining conditions are exactly

\[
\gcd(s_i+\beta_i u,d_i)=1.
\]

For each prime `p | d_i` with `p` not dividing `beta_i`, this excludes the one
residue

\[
u\equiv-s_i\beta_i^{-1}\pmod p.
\]

If `p | beta_i`, that index excludes nothing because `gcd(s_i,d_i)=1`.
Different primes combine by CRT. With four selected depths at most four
residues are forbidden modulo any prime, so only `p=2` or `p=3` can cover the
entire prime modulus automatically.

## Scope

This is a deterministic reduction, not an existence theorem. A family-wide
coarse-selector no-go still requires control of the small-prime covering cases
and of `A` relative to the exact stability intervals. No such unbounded-family
bound is currently registered. The reduction does not constrain full centered
phase residues and does not imply `D`, eventual return, or V1.

V1 remains open.
