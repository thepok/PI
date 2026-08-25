# T106--T141 five-adic phase-flexibility no-go

Status: `proof sketch` overall; exact actual-BBP subsection: `machine-checked`

Date: 2026-08-25 UTC

Sources: ChatGPT Pro memos
`workflows/state/chatgpt-pro/20260825-open-frontier-creative-av/answer.md` and
`workflows/state/chatgpt-pro/20260825-open-frontier-creative-ba/answer.md`,
after independent arithmetic and quantifier audits against `main`.  The named
exact actual-BBP statements in the first subsection are now checked in
T157--T158.  The fixed-precision compression, countermodels, and shadow
constructions remain not Lean-checked.

## Exact actual valuation and forcing pulses

Put

\[
 Q_m=10^m\operatorname{bbpPartial}(7m),\qquad
 \ell_m=\lfloor\log_5(56m+5)\rfloor,\qquad s_m=m-\ell_m.
\]

T141 machine-checks `padicValRat 5 Q_m >= s_m` for `m>=2`.  T157
[`T157T157ExactBBPFiveAdicShell.lean`](../../../../TheoryLib/PiQuantitativeBlockHitting/T157T157ExactBBPFiveAdicShell.lean)
strengthens this to the exact, no-burn-in theorem
`Theory.PiDigits.T157ExactBBPFiveAdicShell.scaledBBPRat_five_val_eq`: for
every `m : Nat`, including `m=0,1`,

\[
 \boxed{v_5(Q_m)=s_m}.
\]

Writing `T_m=5^ell_m`,

\[
 \eta_m=\mathbf 1_{T_m\le14m+1},\qquad
 U_m=5^{-s_m}Q_m\in\mathbb Z_{(5)},
\]

the leading unit is

\[
 \boxed{U_m\equiv2^m(4+2\eta_m)\pmod5},
\]

and is nonzero.  More precisely, T157 checks the normalized residue in
`Theory.PiDigits.T157ExactBBPFiveAdicShell.normalized_bbpPartial_five_congruent`
and the displayed leading unit in
`Theory.PiDigits.T157ExactBBPFiveAdicShell.scaledBBPFiveUnit_five_congruent`.
The unit conclusions are separately checked by
`Theory.PiDigits.T157ExactBBPFiveAdicShell.scaledBBPFiveUnit_five_val` and
`Theory.PiDigits.T157ExactBBPFiveAdicShell.scaledBBPFiveUnit_ne_zero`.  The
proof isolates the one maximal-valuation term from the `8k+1` or `8k+5` pole
and the optional `2k+1` term; all other pole terms vanish after normalization
modulo five.  This is a statement about the rational value in the
localization `Z_(5)`, not about an unreduced or raw numerator.

T158
[`T158T158ExactBBPFiveAdicPulses.lean`](../../../../TheoryLib/PiQuantitativeBlockHitting/T158T158ExactBBPFiveAdicPulses.lean)
checks the forcing identity
`Theory.PiDigits.T158ExactBBPFiveAdicPulses.sampledBBPForcingRat_eq_scaledBBPRat_sub`
and the consecutive-shell dichotomy
`Theory.PiDigits.T158ExactBBPFiveAdicPulses.fiveShellLog_succ_eq_or`.
Consequently `ell_(m+1)-ell_m` is zero or one and
`s_(m+1)<=s_m+1`.  For the **actual positive seven-term BBP forcing**

\[
 F_m^\pi=Q_{m+1}-10Q_m,
 \qquad
 \boxed{\operatorname{padicValRat}_5(F_m^\pi)\ge s_{m+1}}.
\]

For `m>=1`, its reduced denominator is therefore prime to five and its reduced
numerator is divisible by
`5^(m+1-floor(log_5(56m+61)))`.  (At the exceptional forcing index `m=0`, the
exact valuation is `-1`, so that denominator corollary is intentionally not
asserted.)  More precisely, the exact leading-unit computation gives the
following machine-checked pulse law:

- if `ell_(m+1)=ell_m+1`, then `v_5(F_m^pi)=s_(m+1)`
  (`Theory.PiDigits.T158ExactBBPFiveAdicPulses.sampledBBPForcingRat_five_val_eq_of_shell_jump`);
- if `ell_(m+1)=ell_m` but `eta_(m+1) != eta_m`, then again
  `v_5(F_m^pi)=s_(m+1)`
  (`Theory.PiDigits.T158ExactBBPFiveAdicPulses.sampledBBPForcingRat_five_val_eq_of_secondary_activation`);
- if both `ell` and `eta` are unchanged, then
  `v_5(F_m^pi) >= s_(m+1)+1`
  (`Theory.PiDigits.T158ExactBBPFiveAdicPulses.sampledBBPForcingRat_five_val_ge_of_quiet_shell`).

Only the first two cases assert exact valuation; higher cancellation in a
quiet shell is left open.  These laws use the actual BBP pole coefficients,
but do not themselves imply any Archimedean phase cancellation.

At fixed five-adic precision `R`, the same calculation represents `U_m mod
5^R` using fewer than `5^R/2+4` pole terms.  This is only a finite-shell
compression of the representation, not a distribution theorem or a promoted
frontier result.

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

## Growing-modulus actual-value shadow

The fixed-modulus restriction can be removed almost to the natural decimal
scale.  For every `alpha in (0,1)` and `m>=2`, the audited BA construction
chooses

\[
 \widehat Q_m=\frac{a_m}{2^{27m}},\qquad a_m\text{ odd},
\]

in the unique Chinese-remainder lattice class satisfying

\[
 \boxed{v_5(\widehat Q_m-Q_m)\ge m-1}
\]

and with scaled error

\[
 \frac25\rho^m\le
 \tau_m:=10^m\alpha-\widehat Q_m
 <\frac45\rho^m.
\]

The congruence here is explicitly a congruence of the **rational values** in
`Z_(5)`: equivalently it uses `a_m * (2^(27m))^(-1) mod 5^(m-1)`.  It is not a
claim that the raw numerator `a_m` equals or copies a chosen numerator of
`Q_m` modulo that power.

The lattice spacing is `(2/5) rho^m`, so these choices give strictly
increasing lower approximations and positive coboundary forcing

\[
 \widehat F_m=\widehat Q_{m+1}-10\widehat Q_m
              =10\tau_m-\tau_{m+1}>0.
\]

They also satisfy

\[
 \boxed{v_5(\widehat F_m-F_m^\pi)\ge m}.
\]

Indeed, the two differences in
`(Qhat_(m+1)-Q_(m+1))-10*(Qhat_m-Q_m)` have valuation at least `m`.
Moreover `v_5(Qhat_m)=v_5(Q_m)=m-ell_m`, and normalization by this forced
power copies `ell_m-1` residual five-adic unit digits.  Applied to the
word-omitting `alpha_(a,b)` below, the construction also inherits the exact
leading-unit and forcing-pulse laws while retaining prefix-floor recovery and
maximally coherent primitive sums.

This is a materially stronger but still scoped separator: standalone
five-adic rational-value residues through `5^(m-1)`, and forcing residues
through `5^m`, do not force decimal dispersion.  It does **not** preserve the
actual coupled numerator/denominator data, the actual odd denominator, or the
literal seven-term/four-pole BBP structure.

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
one-sided geometric tail, positivity, T141 five-adic valuation data, the
two-primary denominator scale, or standalone rational-value residues through
`5^(m-1)` (with the corresponding forcing residues through `5^m`).  It
strictly strengthens the earlier finite-three-adic-fiber and denominator-grid
separators by preserving these properties simultaneously.

It does **not** preserve the actual full reduced BBP numerator, the odd
denominator/cofactor, their coupled residue, the four-pole coefficients, the
literal seven-term decomposition of the counterfeit forcing, or the exact
BBP partial sums.  The exact valuation and pulse laws concern the actual
forcing, but do not transfer that missing seven-term/four-pole and
odd-denominator coupling to the countermodel.  Those are precisely the kinds
of arithmetic information a surviving BBP route must use.

The universal natural horizon `N=q` is already retired elsewhere, and this
note does not revive it.  Target-dependent witnesses at later horizons remain
live, as do signed/off-diagonal estimates for the actual coupled `(U_m,D_m)`
phases.  Nothing here proves such an estimate, T139, V1, density, or
normality.
