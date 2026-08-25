# T106--T141 five-adic phase-flexibility no-go

Status: `proof sketch`

Date: 2026-08-25 UTC

Source: ChatGPT Pro memo
`workflows/state/chatgpt-pro/20260825-open-frontier-creative-av/answer.md`,
after an independent arithmetic and quantifier audit against `main`.  The
arguments below are not Lean-checked.

## Actual forcing valuation

Put

\[
 Q_m=10^m\operatorname{bbpPartial}(7m),\qquad
 \ell_m=\lfloor\log_5(56m+5)\rfloor,\qquad s_m=m-\ell_m.
\]

T141 machine-checks `padicValRat 5 Q_m >= s_m` for `m>=2`.  Since
`ell_(m+1)-ell_m` is either zero or one, `s_(m+1)<=s_m+1`.  The exact T106
recurrence and the non-Archimedean triangle inequality therefore give, for
the **actual positive seven-term BBP forcing**

\[
 F_m^\pi=Q_{m+1}-10Q_m,
 \qquad
 \boxed{\operatorname{padicValRat}_5(F_m^\pi)\ge s_{m+1}}.
\]

Thus its reduced denominator is prime to five and its reduced numerator is
divisible by
`5^(m+1-floor(log_5(56m+61)))`.  This is a lower bound, not an assertion that
the displayed exponent is the exact valuation.

## Universal envelope countermodel

Let

\[
 \rho=\frac5{2^{27}},\quad D_m=2^{27m},\quad
 \mu_m=\frac{5^{s_m}}{D_m}=\frac{\rho^m}{5^{\ell_m}},\quad
 \Lambda_m=\left\{\frac{5^{s_m}r}{D_m}:r\in\mathbb Z, r\text{ odd}\right\}.
\]

The lattice spacing is `2 mu_m`.  Hence every real interval of length
`rho^m` contains at least

\[
 \frac{5^{\ell_m}-1}{2}>\frac{28m}{5}
\]

members of `Lambda_m`.  Each is reduced, has denominator exactly `2^(27m)`,
and has numerator divisible by `5^s_m`.

For every `alpha in (0,1)`, choose `R_m in Lambda_m` with

\[
 2\mu_m\le 10^m\alpha-R_m\le4\mu_m
\]

and define

\[
 P_m=R_m/10^m,\qquad \tau_m=10^m(\alpha-P_m),\qquad
 F_m=R_{m+1}-10R_m.
\]

Because `mu_(m+1)/mu_m <= 5/2^27`, these are strictly increasing lower
approximations `P_m<P_(m+1)<alpha`, with

\[
 0<\alpha-P_m<16^{-7m},\qquad 0<\tau_m<\rho^m,
\]

and they preserve all of the following envelope data:

- exact denominator `2^(27m)` and T141-scale numerator divisibility;
- positive forcing `F_m>0`;
- `R_(m+1)=10R_m+F_m`;
- the exact coboundary `F_m=10 tau_m-tau_(m+1)`;
- `padicValRat 5 F_m >= s_(m+1)`;
- the exact circle identities for the sampled shadow and the prescribed
  decimal orbit.

For very small `alpha`, finitely many early `P_m` can be negative; therefore
this is deliberately called a *strictly increasing lower approximation*, not
a positive rational approximation.  It is eventually positive, and the
explicit countermodel below is positive at every displayed depth.

The comparison with the actual BBP two-primary scale has only `proof sketch`
provenance: the archived denominator audit gives
`v_2(den Q_m)=27m` at positive even sampled depths.  It is a cofinal scale
match, not a new machine-checked all-depth denominator theorem.

## Word omission and primitive Fourier failure

Given a nonempty decimal word `w`, choose `1<=a<b<=8` so that a digit of `w`
is absent from `{a,b}`, and set

\[
 \alpha_{a,b}=\frac a9+(b-a)\sum_{j=2}^{\infty}10^{-j!}.
\]

Its canonical decimal expansion uses only `a` and `b`, so it omits `w`; it
has no nine-tail ambiguity and is Liouville.  If
`x_n={10^n alpha_(a,b)}`, `N_J=(J+1)!`, and
`S_h(N)=sum_(n<N) exp(2 pi i h x_n)`, then

\[
 \left|\frac{S_h(N_J)}{N_J}-e^{2\pi iha/9}\right|
 \le \frac2{J+1}+\frac{140\pi|h|}{81N_J}.
\]

Consequently, for every `H_J=o(N_J)`,

\[
 \min_{1\le |h|\le H_J}\frac{|S_h(N_J)|}{N_J}\longrightarrow1.
\]

Thus even the primitive frequencies can be asymptotically maximally coherent
on an expanding window while all of the envelope invariants above hold.  The
chosen errors are below `1/9`, while every fractional decimal tail lies in
`[1/9,8/9]`; therefore the shadows also recover the exact canonical decimal
prefix floors.

For the fixed target cylinder, the T128 kernel is strictly negative at
`c=a/9`: `c` is strictly outside the cylinder, is not a cylinder boundary,
and

\[
 q(c-c_{q,A})=qa/9-A-1/2\notin\mathbb Z,
\]

so the Fejer factor does not vanish.  Hence the corresponding directional
defect tends to a value strictly above the T139 zero mode.  The fixed-`q`
endpoint contribution is `O(1/N_J)`, leaving a macroscopic primitive-sum
obstruction.

## Exact scope

This separator retires any implication that uses only the T106 recurrence,
one-sided geometric tail, positivity, T141 five-adic lower bounds, the
two-primary denominator scale, and finitely many fixed-modulus residues.  It
strictly strengthens the earlier finite-three-adic-fiber and denominator-grid
separators by preserving these properties simultaneously.

It does **not** preserve the actual full reduced BBP numerator, the odd
denominator/cofactor, their coupled residue, the four-pole coefficients, the
literal seven-term decomposition of the counterfeit forcing, or the exact
BBP partial sums.  Proposition 1 concerns the actual forcing, but does not
transfer that missing seven-pole/odd-denominator coupling to the countermodel.
Those are precisely the kinds of arithmetic information a surviving BBP
route must use.  Nothing here proves a cancellation estimate for pi, T139,
V1, density, or normality.
