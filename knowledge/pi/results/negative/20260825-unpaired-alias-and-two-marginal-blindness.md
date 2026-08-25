# Unpaired alias residual and two-marginal blindness

Status: `proof sketch`

Date: 2026-08-25 UTC

This note records two independently audited, sharply scoped obstructions from
the ChatGPT Pro AY memo. They concern an unpaired digit observable and abstract
two-marginal occupancy laws. Neither construction models the actual joint BBP
dynamics, so neither is an actual-pi logical separator or a no-go for
joint/off-diagonal arithmetic methods.

## Exact moving alias spectrum

For `q >= 2` and `1 <= r <= q-1`, define the unpaired digit character

\[
D_{q,r}(x)=e_q(r\lfloor qx\rfloor),\qquad 0\le x<1.
\]

Cellwise integration gives the exact Fourier coefficients

\[
\widehat D_{q,r}(\ell)=
\begin{cases}
\displaystyle\frac{q(1-e(-r/q))}{2\pi i\ell},
&\ell\equiv r\pmod q,\\[2mm]
0,&\ell\not\equiv r\pmod q.
\end{cases}
\]

Thus the bare digit factor has an infinite `1/|ell|` alias tail and a genuine
boundary discontinuity. At every decimal scale, take `r=q/2`. Its support is
`ell=(2j+1)q/2`, with coefficient magnitude `2/(pi|2j+1|)`. Only
`ell=+-q/2,+-3q/2` lie in the natural window `|ell|<=2q-1`. Parseval therefore
gives the exact scale-independent residual

\[
\boxed{
\inf_{\operatorname{supp}\widehat P\subset[-2q+1,2q-1]}
\|D_{q,q/2}-P\|_2^2
=1-\frac{80}{9\pi^2}>0.}
\]

Hence an unpaired digit character cannot be replaced in `L^2` by a
natural-window trigonometric polynomial with vanishing error. This does not
apply to the matched digit/successor character: the exact decimal-shift
identity cancels its alias tail and selects one ordinary frequency. It also
does not prove that the actual pi orbit visits the discontinuity layer with
any particular frequency.

The separate eventual-zero-carry consequence of the external hypothesis
`IrrationalityMeasureBelow Real.pi 8` was already recorded in the repository;
it is not new progress from AY and supplies no cancellation estimate.

## Sharp blindness of separate CRT marginals

Let `A=2^k`, `B=5^k`, `q=AB`, and translate the omitted target to `(0,0)` in
`Z/AZ x Z/BZ`. For a probability law `mu` with uniform `A`- and `B`-marginals
and `mu(0,0)=0`, write

\[
\widehat\mu(s,t)=\mathbb E_\mu[e_A(sX)e_B(tZ)].
\]

The pure marginal characters vanish. Orthogonality at the omitted target
then yields

\[
1+\sum_{s\ne0,\ t\ne0}\widehat\mu(s,t)=0.
\]

Since there are `(A-1)(B-1)` mixed characters,

\[
\max_{s\ne0,\ t\ne0}|\widehat\mu(s,t)|
\ge\frac1{(A-1)(B-1)}.
\]

This is sharp. An optimizer is

\[
\mu_*(0,0)=0,
\quad
\mu_*(0,z)=\frac1{A(B-1)},
\quad
\mu_*(x,0)=\frac1{B(A-1)},
\]

for nonzero displayed coordinates, and

\[
\mu_*(x,z)=\frac{AB-A-B}{AB(A-1)(B-1)}
\quad(x\ne0,z\ne0).
\]

It has uniform marginals and

\[
\boxed{
\widehat\mu_*(s,t)=-\frac1{(2^k-1)(5^k-1)}
\quad(s\ne0,t\ne0).}
\]

Thus even perfect cancellation of every separate `2^k`- and `5^k`-marginal
character is compatible with omission of the joint target. The corresponding
centred singleton has mixed-sector Fourier energy

\[
\frac{(2^k-1)(5^k-1)}{10^{2k}},
\]

which is the fraction

\[
\frac{(2^k-1)(5^k-1)}{10^k-1}\longrightarrow1
\]

of its total centred energy.

This closes only proofs whose genuinely new input is separate control of the
two CRT marginals. The optimizer is an abstract finite occupancy law, not a
stationary overlapping decimal process and not a sequence constrained by the
actual BBP numerator/denominator recurrence. Joint characters, overlap-aware
dynamics, and target-signed/off-diagonal estimates for the actual
`(U_m,D_m)` phases remain live.
