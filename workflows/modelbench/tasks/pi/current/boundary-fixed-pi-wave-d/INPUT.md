# Exact boundary-matched PI frontier (2026-08-24)

Let `x_n=fract(10^n*pi)`, `S_h(N)=sum_(n<N)e(h*x_n)`, and `q=10^k`. For a
word interval `[a,a+1/q)`, center `c=a+1/(2q)`. For any finite real coefficient
system `C_q(h)`, the directional defect is exactly

`D_q(N,a)=-(1/N) Re sum_(h != 0) C_q(h)e(-h*c)S_h(N)`.

It may be negative. The verified comparison is `D_q <= unsigned aggregate
load`, never the reverse. For the boundary-matched kernel

`K_q(t)=(cos(2*pi*t)-cos(pi/q))*F_q(t)^2`,

Lean verifies its exact finite Fourier form, nonpositivity outside the word
interval, positive zero mode, and: `D_q(N,a)<C_q(0)` forces a word hit. Lean
also verifies

`C_q(0)=[2(q^2-1)-(2q^2+1)cos(pi/q)]/(3q)`

and `A_q(0)=(q^2+2)/(3q^3)<C_q(0)` for every `q>1`, where `A` is Jackson.
The normalized nonzero coefficient domination and q=10 boundary separators
are only audited proof sketches. Fixed-pi smallness is completely open.

Exact dynamics: `S_(10h)(N)=S_h(N)-e(h*x_0)+e(h*x_N)`. Do not confuse
prefix-extension geometry with digit deletion: if `a'=a+d/(10q)`, generally
`10a'` is not `a` modulo one. Do not assume `A_(10q)(10h)=A_q(h)/10`; it is
false. Wordwise V1 needs, for each word, existence of one `N>0`; failure only
for all sufficiently large N does not refute it.

The sparse decimal alpha no-go proves that effective irrationality, periodic-
window exclusion, digit changes, fixed-frequency gaps, and moving-mesh UI by
themselves do not supply the estimate. BBP/Machin work must retain exact
reduced numerator or coefficient phase; common-denominator size alone is a
known dead end. Nothing here proves V1, density, normality, or fixed-pi
cancellation.
