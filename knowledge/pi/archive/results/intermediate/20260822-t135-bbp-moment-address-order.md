# T135: BBP moment positivity and address-tail order

Status: `proof sketch`

Source: ChatGPT Pro hard-math exploration, independently audited. Raw answer
SHA-256: `e0dc58a77eff2a57ebd672101d0dd03fd57208cc9a5766a88172028d09613ce6`.

## Scope first

These identities use the full exact centered phase residues to reconstruct the
canonical entry and then use the global tail `pi-A_m`. They do not follow from
the coarse `(z,sign,bad)` address, never use the literal all-BAD inequalities,
and do not prove a hit. They are coefficient/tail lemmas, not a resolution of
`D` or V1.

## Hausdorff-moment representation

Set `A_(-1):=0` and let

\[
b_k=A_k-A_{k-1}=\frac{\nu_k}{16^kD_k},\qquad
\nu_k=120k^2+151k+47.
\]

The BBP partial fraction identity is

\[
\frac{\nu_k}{D_k}=\frac4{8k+1}-\frac2{8k+4}
-\frac1{8k+5}-\frac1{8k+6}.
\]

With

\[
t(x)=\frac{x^8}{16},\qquad
w(x)=4-2x^3-x^4-x^5
=(1-x)(x^2+2)(x^2+2x+2),
\]

one has `w(x)>0` for `0<=x<1` and

\[
b_k=\int_0^1t(x)^kw(x)\,dx.
\]

Thus `(b_k)` is a strict Hausdorff-moment sequence supported in
`[0,1/16]`. For

\[
R_m=\pi-A_m=\sum_{k=m+1}^{\infty}b_k,
\]

geometric summation gives

\[
R_m=\int_0^1\frac{t(x)^{m+1}}{1-t(x)}w(x)\,dx.
\]

In particular the relevant Hankel minor is strict:

\[
b_{m+1}b_{m+3}-b_{m+2}^2>0.
\]

## Exact reconstruction and positive functional

For the selected pair at physical checkpoint `m`, write

\[
C_{m,s}=\frac14+\delta(m,\ell_m+s),\qquad
Q_{m,s}=\frac{q_{J_m+s}}{48},
\]

and

\[
z_{m,s}=C_{m,s}+Q_{m,s}x_m-y_{m,s},\qquad
\kappa_m=z_{m,0}-10z_{m,-1}.
\]

Since `Q_(m,0)-10Q_(m,-1)=3`, the full exact pair record reconstructs

\[
x_m=\frac{\kappa_m+y_{m,0}-10y_{m,-1}-C_{m,0}+10C_{m,-1}}3.
\]

This uses the exact `y` values, not merely their signs or BAD status.

The elementary bounds `A_0=47/15<=A_m<pi<22/7` put
`48A_m-573/4` strictly between 7 and 8. Hence

\[
x_m=48A_m-\frac{601}{4}.
\]

Put

\[
\Theta=48\pi-\frac{601}{4},\qquad
U_m=\Theta-x_m=48R_m,
\]

\[
V_m=\frac{U_m}{16}-U_{m+1},
\]

and

\[
K_m=(U_m-U_{m+1})(U_{m+2}-U_{m+3})
 -(U_{m+1}-U_{m+2})^2.
\]

Then

\[
K_m=48^2\bigl(b_{m+1}b_{m+3}-b_{m+2}^2\bigr)>0,
\]

while moment support gives `U_m>0` and `V_m>0`. Therefore

\[
H_m:=U_mV_mK_m>0.
\]

This involves the three individual increments `b_(m+1),b_(m+2),b_(m+3)`,
but it is canonical tail positivity expressed in lossless phase coordinates;
it is not an all-BAD carry restriction.

## Exact translation stress tests

Under a common no-wrap entry translation `x_r -> x_r+tau`,

\[
U_r(\tau)=U_r-\tau,\qquad
V_r(\tau)=V_r+\frac{15}{16}\tau,\qquad
K_r(\tau)=K_r.
\]

Thus

\[
H_m(\tau)=(U_m-\tau)
\left(V_m+\frac{15}{16}\tau\right)K_m,
\]

and the positive component containing the canonical entry is

\[
-\frac{16}{15}V_m<\tau<U_m.
\]

For the exact translated comparator

\[
x_m^*=\frac{63}{64}+48(A_m-A_n),\qquad m\ge n\ge6,
\]

the common translation is `tau_n=63/64-x_n`. Exact rational bounds give no
wrap and

\[
H_m(\tau_n)<-\frac{1035}{8192}K_m<0.
\]

This is a uniform sign and normalized-by-`K_m` separation, not a uniform
absolute margin because `K_m` tends to zero.

There is also an explicit unbounded scalar-phase-fiber stress test. Let

\[
T_m=M_m/48,\quad Q_m=q_{J_m}/48,\quad d_m=\gcd(Q_m,T_m),
\]

and

\[
\mathcal F_{41}=\{m\ge6:J_m\equiv3\pmod5\}.
\]

Strict increase of `J_m` together with `J_m/m -> 1+log_10(8/5)<5/4`
implies that every residue class modulo 5, hence `F_41`, occurs infinitely
often. For `m>=6`, one has `J_m>=4` and `10^(J_m)=16 (mod 48)`, so
`Q_m=q_(J_m)/48` is an integer. For `m` in this family, `41|q_(J_m)`;
because `gcd(41,48)=1`, this gives `41|Q_m`. Also `41|T_m`, so `41|d_m`.
The lift

\[
e\longmapsto e+T_m/d_m,\qquad x\longmapsto x+1/d_m
\]

preserves the single selected `Q_m x` phase modulo one. It does not preserve
the entire two-phase absolute `(z,sign,bad)` record. Exact tail bounds give no
wrap and, at the next checkpoint,

\[
H_{m+1}(1/d_m)<-99b_{m+1}^2K_{m+1}<0.
\]

This is a valid unbounded scalar-fiber sign separation, but it remains
orthogonal to an all-BAD-to-hit implication.

## Address-tail sawtooth

Define

\[
W_m=q_{J_m}R_m=\frac{q_{J_m}}{48}U_m,\qquad
h_m=J_{m+1}-J_m\in\{1,2\}.
\]

For `m>=6`, the exact summand-ratio bounds imply

\[
\frac1{100}<\frac{R_{m+1}}{R_m}<\frac1{16}.
\]

Consequently `W` decreases across a one-step address jump and increases across
a two-step jump:

\[
(2h_m-3)(W_{m+1}-W_m)>0.
\]

This is an exact coefficient-tail/address-order coupling. Neither `W_m` nor
`h_m` uses the literal BAD predicate, and known canonical bad blocks coexist
with the inequality.

## Rejected extrapolation and next test

The Pro answer's claimed arbitrary-degree polynomial STOP is not retained.
Factoring a canonical-only polynomial after adjoining `x_m` is tautological and
does not rule out a coefficient-defined polynomial over the original field.

The only plausible bridge left by these lemmas is an exact implication from
the literal all-BAD half-open inequalities to a signed-variation inequality
opposite to the unconditional sawtooth sign. Such a bridge has not been found.
It must survive exact checks against known canonical bad runs and the T134
counterstates before it can be stated even as a conjecture.

V1 remains open.
