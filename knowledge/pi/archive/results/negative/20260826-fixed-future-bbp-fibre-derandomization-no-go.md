# Fixed-future BBP fibre de-randomization no-go

Status: `proof sketch`

Source: independently audited from
`workflows/state/chatgpt-pro/20260825-open-frontier-creative-bc/turns/0004/answer.md`.

This note closes only the proposed implication

```text
fixed-future fibre majority
+ existing fixed-K dyadic isometry
+ a harmless stable/complementary CRT state
=> the distinguished lift t=0 is good.
```

It proves no target-signed estimate for the actual pi orbit.

## The artificial fibre is a translated uniform grid

Fix `k>=3`, `q=10^k`, a target `a<q`, and

\[
 L=4800(k+1)q,\qquad n\ge4k+6\text{ even},\qquad T=n+L.
\]

Write the reduced fixed-future BBP rational as

\[
 Q_T=10^TB_T=\frac{5^L U_T}{2^{27T}R_T},
\]

where `R_T` is odd, `5 \nmid R_T`, and `gcd(U_T,2R_T)=1`.  Put

\[
 A_T=27T+L,\quad M=2^{A_T-k-1},\quad
 \lambda_t=1+2^{k+1}R_T5^kt\quad(0\le t<M),
\]

and define

\[
 z_j(t)=\{\lambda_t10^{n+j}B_T\},\quad
 \xi_{n,T}=\{10^nB_T\},\quad \eta_T=5^kU_T.
\]

Then `eta_T` is odd and the exact identity is

\[
 \boxed{z_j(t)=\left\{10^j\left(\xi_{n,T}+\frac{\eta_Tt}{M}\right)\right\}}
 \qquad(j\ge0).
\]

Thus, for the exact T139 primitive polynomial `P_(q,a)` and its Birkhoff
polynomial

\[
 S_{q,a,L}(x)=\sum_{j=0}^{L-1}P_{q,a}(10^jx),
\]

the lifted score is

\[
 Z_{n,k,a}(t)=S_{q,a,L}\left(\xi_{n,T}+\frac{\eta_Tt}{M}\right).
\]

Multiplication by the odd unit `eta_T` permutes `Z/MZ`.  The fibre moments
are therefore ordinary quadrature on one translated uniform dyadic grid.
The odd numerator and denominator disappear from those moments, but not from
the translation `xi_(n,T)`, the labelling permutation, or the distinguished
identity point `t=0`.

## A miss makes the distinguished lift rigidly bad

Let

\[
 \rho=\frac{10}{16^7},\qquad
 \Lambda_T=(56T+9)(56T+10).
\]

The T164 tail estimate and the coefficient bound
`sum_u u*|p_(q,a)(u)|<5q` give, whenever `H<=T-n`,

\[
 \left|S_{q,a,H}(10^nB_T)-S_{q,a,H}(10^n\pi)\right|
 <\frac{10\pi q}{9}\frac{\rho^T}{\Lambda_T}.
\]

For the displayed parameters this error is less than `1`.  If the actual
length-`L` pi block starting at `n` misses the target cylinder, the exact
empty-cylinder obstruction and endpoint budget give

\[
 \operatorname{Re}S_{q,a,L}(\{10^n\pi\})
 <-\frac{L}{12q}-(395k+400).
\]

Consequently the distinguished fixed-future lift satisfies

\[
 \boxed{
 \operatorname{Re}Z_{n,k,a}(0)
 <-\frac{L}{12q}-(395k+399).
 }
\]

This is compatible with more than `307/400` of the artificial lifts being
good: a large subset need not contain its distinguished point.

The obstruction is locally stable.  Set

\[
 \delta_k=395k+399,\qquad
 r_k=\frac{9\delta_k}{20\pi q(10^L-1)}<\frac12.
\]

The Lipschitz bound

\[
 \operatorname{Lip}(S_{q,a,L})
 <\frac{10\pi q}{9}(10^L-1)
\]

shows that every grid point within circle distance `r_k` of the identity is
still below the good threshold by at least `delta_k/2`.  The no-wrap estimate
`M>4q10^(L-1)` gives

\[
 Mr_k>\frac{9\delta_k}{50\pi}>90
 \qquad(k\ge3).
\]

Hence at least `2*floor(M*r_k)+1 >= 181` fibre points in the actual
Archimedean grid neighbourhood of the identity are bad.  Continuity cannot
select a nearby good conjugate.

## Fixed local modulus is the wrong physical frequency

At a positive even sampled depth `m`, write the delayed full phase with
dyadic exponent

\[
 A_m=27m+k.
\]

If `Y_(m,k)` denotes its two-local unit, the fixed-modulus character is the
dyadic factor of the full phase only after the conversion

\[
 e_{2^K}(sY_{m,k})
 =\chi_{2,m}\!\left(s2^{A_m-K}\right).
\]

Thus the associated physical frequency is

\[
 \boxed{h_{m,K,s}=s2^{27m+k-K}},
\]

which is multiplied by `2^54` when `m` advances by two.  Conversely, for a
fixed natural frequency `h=2^r s` with `s` odd, the required local modulus is

\[
 K_m=27m+k-r,
\]

and itself grows by `54` every two depths.  The existing fixed-`K`
Ramanujan permutation theorem and a fixed T139 natural frequency therefore
do not describe the same temporal character.

## The full odd complement reverses the dyadic character

Let

\[
 Q_m=\operatorname{scaledBBPRat}(m),\quad
 F_m=Q_{m+1}-10Q_m,\quad
 W_m=2^{27m}Q_m,
\]

and, at positive even `m`, define

\[
 \Gamma_m=W_{m+2}-25\,2^{56}W_m.
\]

There is an exact matched two-step identity

\[
 \boxed{
 \frac{\Gamma_m}{2^{27(m+2)}}
 =Q_{m+2}-100Q_m=10F_m+F_{m+1}.
 }
\]

Assume the delay-`k` burn-in and reduce

\[
 G_{m,k}=\frac{\Gamma_m}{5^k}=\frac{g_m}{b_m},
 \qquad b_m\text{ odd},\qquad A_m^\Gamma=27(m+2)+k.
\]

Define the complete dyadic and odd CRT characters

\[
 \chi_{2,m}^{(k)}(h)
 =e_{2^{A_m^\Gamma}}(h g_m b_m^{-1}),\qquad
 \chi_{o,m}^{(k)}(h)
 =e_{b_m}(h g_m 2^{-A_m^\Gamma}).
\]

CRT and the two-step identity give

\[
 \chi_{2,m}^{(k)}(h)\chi_{o,m}^{(k)}(h)
 =e\!\left(\frac{h}{q}(10F_m+F_{m+1})\right),
\]

or, with the essential conjugation displayed,

\[
 \boxed{
 \chi_{o,m}^{(k)}(h)
 =\overline{\chi_{2,m}^{(k)}(h)}\,
   e\!\left(\frac{h}{q}(10F_m+F_{m+1})\right).
 }
\]

For `0<|h|<2q`, T164's forcing bound implies

\[
 \left|\chi_{o,m}^{(k)}(h)
   -\overline{\chi_{2,m}^{(k)}(h)}\right|
 <\frac{4\pi(100+10\rho)}{\Lambda_m}\rho^m.
\]

Across even depths `M,M+2,...,M+2N-2` satisfying the burn-in hypotheses,

\[
 \boxed{
 \left|\sum_{j=0}^{N-1}
   \chi_{2,M+2j}^{(k)}(h)\chi_{o,M+2j}^{(k)}(h)-N\right|
 <\frac{4\pi(100+10\rho)}{1-\rho^2}
   \frac{\rho^M}{\Lambda_M}.
 }
\]

The full matched character is therefore nearly maximally coherent exactly
where its dyadic marginal has fixed-modulus Ramanujan cancellation.  This is
matched two-step resonance and CRT packaging, substantially overlapping the
T160 resonant extraction and T164 tail control.  It is **not** an estimate of
an individual, unpaired T139 phase.

## Claim boundary

The retired mechanism is only the combination of artificial fibre majority,
the existing fixed-`K` dyadic isometry, and an assumed harmless odd
complement as a way to prove `t=0` good.  Still open are a direct theorem for
the distinguished translated-grid point, a growing-modulus argument retaining
the full odd state, the full unpaired moving-conductor character at a fixed
natural frequency, and every genuinely pi-specific target-signed method.

No T139 or T148 premise, target-cylinder hit, density statement, normality
statement, or V1 consequence is proved here.  Nothing in this note is
Lean-checked.
