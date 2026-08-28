# T189 / fresh-monotone regeneration

Claim status: T189 identities are `machine-checked`; FMR on an unbounded
actual-π path is a `conjecture`.

For a positive natural-diagonal node `(q,A)`, put `Q=10q` and define

```text
G_d = B(Q,A+dq,q) - B(q,A,q),
D_d = B(Q,A+dq,Q) - B(Q,A+dq,q).
```

T189 and the exact potential bookkeeping give

```text
D_d = q(Delta_0 + Xi_d) - 21/10,
```

where `Xi_d` is the real part of the complete nonzero predecessor-character
correlation over the fresh actual-π block. It retains the target factor,
predecessor digit, suffix orbit, and literal boundary coefficients.

Fresh-monotone regeneration is

```text
exists d<10: D_d>0 and G_d+D_d>0.                 (FMR)
```

The minimal honest backward split is

```text
S_+={d<10:D_d>0};
R1: S_+ is nonempty;
R2: exists d in S_+ with G_d+D_d>0.
```

R1 and R2 must share the digit. Separate witnesses, unsigned energy, or a
positive final capital inherited from the old block do not prove FMR.

T177 gives `sum_d Xi_d=0`, hence
`sum_d D_d=10q*Delta_0-21`; this yields a zero-sector sufficient condition,
but it is not known for π. T190 proves a sharp deterministic R2 certificate
from complementary top-set cardinalities, but no suitable actual-π rank
bounds are known.

An audited `proof sketch` gives a smaller aligned alternative. Put

```text
h_d=(-G_d)_+,                 Y_d=D_d-h_d,
hbar=(1/10) sum_d h_d,
hhat_1=(1/10) sum_d h_d*zeta^d,
P_1=C_1+conj(C_9),            zeta=exp(2*pi*i/10).
```

Then `max_d Y_d>0` is exactly FMR. If `gamma_10` is the Minkowski gauge of
the regular decagon `conv{zeta^d:d<10}`, the sharp decagon envelope gives

```text
max_d Y_d >= q*Delta_0 - 21/10 - hbar
             + gamma_10(hhat_1-(q/2)*P_1).          (DC1)
```

Thus strict positivity of the right side is a same-digit FMR certificate. It
retains the inherited deficit direction and only one fresh paired sector,
instead of separating R1 and R2. This is deterministic consumer algebra, not
π arithmetic: no theorem controls the displayed gauge for actual π.

The loss from discarding the direction of `hhat_1` is exactly sharp. Writing
`Dbar=(1/10) sum_d D_d` and `Dhat_1=(q/2)*P_1`, the reverse triangle inequality
gives the weaker sufficient condition

```text
Dbar + gamma_10(Dhat_1) > 2*hbar.                 (DC1-unsigned)
```

The factor `2` cannot be reduced using only `Dbar`, `Dhat_1`, and `hbar`.
For `H>0`, `t>=H`, concentrate `h_j=10H` on one digit and
`u_((j+5) mod 10)=10(t-H)` on its antipode, then take `G=-h` and `D=h-u`.  Here
`Y=D-h=-u<=0`, so FMR fails, while
`Dbar+gamma_10(Dhat_1)=2H=2*hbar`.  Thus an unsigned Pair-R1 estimate cannot
be upgraded to same-digit FMR by a better universal triangle inequality; a
fresh actual-π orientation or independently stronger deficit bound is required.

## Corrected full-sector cross-energy rung

Claim status: deterministic algebra is a `proof sketch`; the hard-node check
below is an outward-interval `experiment`.

Put `F_d=G_d+D_d`, write `x^- = max(0,-x)`, and define

```text
E(D,F) = sum_d D_d*F_d - sum_d D_d^-*F_d^-.
```

Coordinatewise sign decomposition gives exactly

```text
E(D,F) = sum_d D_d^+*F_d^+
       - sum_d (D_d^+*F_d^- + D_d^-*F_d^+).
```

Therefore `E(D,F)>0` implies literal same-child FMR.  It is strictly
sufficient, not equivalent: for example, `D=(1,1,0,...)` and
`F=(1,-2,0,...)` have an FMR digit but `E=-1`.  The coefficient one on the
common-negative correction is the smallest universally safe coefficient over
unrestricted real vectors, since `D=F=(-1,0,...)` defeats every smaller one.
No corresponding sharpness claim is made inside the narrower actual T189
state space.

The bilinear part has the exact energy-drift identity

```text
<D,F> = (||D||_2^2 + ||F||_2^2 - ||G||_2^2)/2.
```

With the unnormalized ten-point digit DFT, Parseval gives

```text
<D,F> = (1/10) * (Dhat_0*Fhat_0 + Dhat_5*Fhat_5
          + 2*sum_(r=1)^4 Re(Dhat_r*conj(Fhat_r))).
```

Thus the scalar retains all five real character blocks and their relative
cross-horizon phases.  The coordinatewise overlap correction also retains
the literal same-digit signs; replacing it by an unsigned norm bound is not
equivalent.

At the legally reached actual-π node `(q,A,N)=(10000,1334,10000)`, an
independently rebuilt 100050-digit Chudnovsky certificate and the existing
strict outward-interval replay give

```text
<D,F>              in [89265049882.3045, 89265501752.1400],
sum_d D_d^-*F_d^-  in [86522047117.5054, 86522239004.5691],
E(D,F)             in [2743002764.7990, 2743262747.5709].
```

Here `d=5` is the unique common-positive coordinate and `d=8` the unique
opposite-sign coordinate.  This proves finite non-vacuity at a node where
Pair/DC1, adjacent-pair, parity, and one-block-deleting convex certificates
fail.  It does **not** supply the missing actual-π theorem.  The new arithmetic
target is a pathwise lower bound `E(D,F)>0` at recursively reached growing
horizons, sourced by signed cross-sector alignment and control of the
opposite-sign leakage.

An independently reproduced directed-interval `experiment` separates both
uniform low-sector closures at the actual-π node `(q,A)=(1000,689)`.  It uses
the machine-checked T173 decimal cylinder and the T128/T139 score identity;
the standalone replay is
[`t189_pair_dc1_counterexample_interval.py`](../../../workflows/experiments/t189_pair_dc1_counterexample_interval.py).
The parent has `B(q,A,q)>80.21738`.  All five correctly conjugated Pair-π
margins lie between `-6.71` and `-6.21`, and the DC1 right side is below
`-7199.92697`.  Nevertheless

```text
D_8 > 12295.03615,       G_8+D_8 > 11062.69343,
```

while every other fresh gain is negative.  Thus literal FMR holds uniquely at
`d=8`: several character sectors interfere favorably even though no individual
paired amplitude or first-sector envelope detects the child.  This refutes
uniform Pair-π and universal actual-π positivity of the DC1 premise, not FMR,
the deterministic DC1 theorem, or a pathwise arithmetic use of DC1.

## Adjacent-digit-pair reduction

Claim status: `proof sketch`; the numerical check below is an `experiment`.

There is a smaller strict sufficient consumer that survives this hard node.
Pair the literal digits as `{0,1}`, `{2,3}`, ..., `{8,9}` and put

```text
Theta_j=(Xi_(2*j)+Xi_(2*j+1))/2,
M_j=(Y_(2*j)+Y_(2*j+1))/2,                       0<=j<5.
```

Then exactly

```text
M_j = q*(Delta_0+Theta_j) - 21/10
      - (h_(2*j)+h_(2*j+1))/2.
```

Consequently `M_j>0` implies that the larger of the two literal `Y` values is
an FMR witness.  Equivalently, the required signed estimate is

```text
Theta_j > -Delta_0 + 21/(10*q)
          + (h_(2*j)+h_(2*j+1))/(2*q).
```

This condition is strictly sufficient, not equivalent to FMR.  In the digit
DFT, adjacent averaging multiplies sector `r` by
`(1+zeta^(-r))/2`, so sector `r=5` cancels exactly.  The five fresh values
`Theta_j` sum to zero and hence carry four real degrees; the full `M` vector
also contains the inherited deficit data and is not four-dimensional.

An independent floating reconstruction at `(q,A)=(1000,689)` gives
`M_4 approximately 525.52694622292>0`, so this consumer survives where all
Pair-π margins and the DC1 right side are negative.  This value is not yet a
directed-interval certificate: the existing interval replay certifies the
individual `d=8` FMR margin but does not assert or print `M_4`.

A total recursive selector may choose a maximizing pair and then the larger
`Y` inside that pair.  The actual-π assertion that the selected `M_j` stays
positive at every level is still a `conjecture`, stronger than FMR and not a
source of signed arithmetic.  Even if proved, one ray still needs the separate
word-coverage step recorded in `VERIFIED_CONSUMER_PATH.md`.

There is also a route-specific Machin transfer `proof sketch`.  With
`rho=2/125`, `q=10^K`, the primitive-ray analogue of T169's pointwise phase
bound gives the uniform digitwise buffers

```text
E_G(q) = 20*pi*q*(1+10*rho)*rho^K/(1-rho),
E_D(q) = 200*pi*q*rho^(q+K+1)/(1-rho).
```

The clipping map `x |-> max(0,-x)` is one-Lipschitz, so
`|Y_d-Ytilde_d|<E_G+E_D`.  Therefore a carrier pair with
`Mtilde_j>E_G+E_D` transfers pair positivity; choosing a carrier digit whose
`Ytilde_d` is at least the pair average also transfers that same digit.  T169
supplies only these approximation buffers, not the required carrier sign.
The primitive-ray adaptation and the displayed load-`<5` specialization are
not currently machine-checked.

`experiment` (pinned decimal prefix, floating-point replay): at the literal
natural-diagonal node `(q,A)=(10000,3334)`, the DC1 right side is approximately
`68531.49962346>0`, while `max_d Y_d` is approximately `316729.22974`; the
direct FMR witnesses are `d in {5,6,7,8}`. An independent reconstruction
reproduced these values. This is a finite falsification/viability check, not a
numerical certificate, a machine-checked instance, or evidence of an
unbounded actual-π path.

Finite π replay supplies a positive root and two surviving levels only. The
inductive theorem needed is along one consistently selected unbounded path;
assuming such reached nodes in advance is circular. After transport, a
separate viable-branching or selector-word coverage argument remains.
