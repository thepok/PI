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

There is an exact horizon-energy normalization.  Let `u` and `v` be the old
and final zero-mean nonzero-sector digit vectors, `x=v-u`, let `delta` be the
zero-sector horizon increment, put `theta=21/(10q)`, and
`kappa=R(q)+delta`.  Then

```text
G_d = q*(R(q)+u_d) + 21/10,
D_d = q*(delta+x_d-theta),
F_d = q*(kappa+v_d),

E/q^2 = 10*(delta-theta)*kappa + <x,v> - L,
L = sum_d (theta-delta-x_d)_+ * (-kappa-v_d)_+,
<x,v> = ||x||^2 + <x,u>.
```

There is a sharper exact coordinatewise decomposition.  Put

```text
P = {d : D_d>0 and F_d>0},
O = {d : D_d*F_d<0}.
```

Then, as a `proof sketch`,

```text
E = sum_(d in P) D_d*F_d
    - (1/4)*sum_(d in O) G_d^2
    + (1/4)*sum_(d in O) (|D_d|-|F_d|)^2.
```

Indeed, on an opposite-sign coordinate
`4*|D_d*F_d|=G_d^2-(|D_d|-|F_d|)^2`.  Hence the coefficient-sharp
discarded-imbalance certificate

```text
J0 = sum_(d in P) D_d*F_d - (1/4)*sum_(d in O) G_d^2 > 0
```

implies `E>0`; the factor `1/4` cannot be decreased when only `G_d` is
retained, as equality occurs for `D_d=-a`, `F_d=a`.  Cauchy--Schwarz also
gives the stronger bound

```text
J1 = J0 + (sum_(d in O) (|D_d|-|F_d|))^2/(4*|O|) <= E
```

for nonempty `O`, with `J1=J0` otherwise.  An independent direct replay
reproduces positive `J0/q^2` at the root and seven certified children:

```text
(1000,334)    5882.160729997   (10000,334)   1812.493894892
(10000,1334)    17.272723548   (10000,2334)   356.896831375
(10000,3334)  1242.158016490   (10000,4334)   222.101066736
(10000,8334)  1695.095917187   (10000,9334)   526.220731386
```

These values are floating `experiments`, not outward intervals.  At the hard
node `(10000,1334)`, `P={5}` and `O={8}`, so the short remaining inequality
is exactly `D_5*F_5>G_8^2/4`.  This compression does not create its sign.

The potential defects cancel exactly in `F`.  A tempting stronger split would
ask, for one fixed `0<gamma<1`, for

```text
<x,u> >= -(1-gamma)*||x||^2,
L < 10*(delta-theta)*kappa + gamma*||x||^2.
```

Together these imply `E>0`, but the scale-independent version is false on the
certified π tree.  Writing `Dbar,Fbar` for digit means and

```text
Xraw = sum_d (D_d-Dbar)^2,
Lraw = sum_d D_d^-*F_d^-,
```

the first inequality is equivalent to `gamma<=a` and the second to `gamma>b`,
where

```text
a = <D-Dbar,F-Fbar>/Xraw,
b = (Lraw-10*Dbar*Fbar)/Xraw.
```

Independent exact-rational postprocessing of freshly regenerated outward
intervals gives

```text
(10000,2334):  gamma > 0.753979359184274,
(10000,4334):  gamma <= 0.630504533644287.
```

Thus no fixed `gamma` works at all eight certified nodes; the gap exceeds
`0.12347`. Each node separately has a nonempty interval, but allowing an
arbitrary node-dependent `gamma` supplies no independent π mechanism. Before
the all-child separator below, direct pathwise `E>0` was the candidate proxy;
it is now only a conditional reopening premise, not the active target.

For the actual π orbit, an independently rebuilt 100050-digit Chudnovsky
certificate and the existing strict outward-interval replay show that `E`
loses none of the eight currently certified legal nodes:

```text
(q,A)          rigorous lower bound for E       exact FMR digits
(1000,334)       5889767251.412295664624         0,1,2,3,4,8,9
(10000,334)    181247869486.759928253457         1
(10000,1334)     2743002764.799077303771         5
(10000,2334)    36670125401.084868195691         2,6
(10000,3334)   126068418043.357458948261         5,6,7,8
(10000,4334)    26406342086.320378967932         3
(10000,8334)   169502027654.068868458087         2,3,5
(10000,9334)    52767566481.183813189676         1,2,6
```

At `(10000,1334)`, where the strongest earlier low-dimensional certificates
fail, `d=5` is the unique common-positive coordinate, `d=8` the unique
opposite-sign coordinate, and the full interval is
`E in [2743002764.7990,2743262747.5709]`.  The table is a finite
`experiment`; it does **not** supply the missing actual-π theorem. It once
motivated a pathwise lower bound `E(D,F)>0` at recursively reached growing
horizons, but the all-child separator below pauses that proxy absent a new
actual-π joint-character mechanism.

The next reached node has now been independently replayed with directed
outward intervals (`experiment`). At `(q,A)=(100000,51334)`, the already
recorded FMR digit `d=1` reaches `C=151334` and satisfies

```text
parent P > 83327.50,
fresh D_1 > 1066287.52,
G_1 + D_1 > 3071681.30.
```

An explicit T193-central/T194-type parent atom at time `196299` lifts under
the literal predecessor digit `1` to a child atom at time `196298`; their
normalized central coordinate is exactly equal. A second child atom at time
`487122` has surplus `>225457.32` for the same target `151334` and lies just
outside the T193 chamber. This is genuine additional finite actual-π sign
information, but it does not explain the block sign: after removing the
central child atom the remaining fresh surplus is `<-629252.37`, and after
removing both displayed atoms it is `<-854709.69`. Thus the full `D_1>0`
comes from the independent complete-block computation, not from a two-atom
amplification theorem. The replay reproduced its bundled outputs exactly; it
remains an `experiment`, not a Lean theorem or an unbounded transport.

That source cannot be generic decimal-orbit bookkeeping.  Let `w=uv`, where

```text
u = first 1000 digits of (6666 0^64)^infinity,
v = first 9000 digits of (2666 0^48)^infinity,
alpha = 0.overline(w).
```

The word has SHA-256
`8e896b260071cfcde983fe89d509cfbf007ef6a0d25d773bf72d3545c346496c`.
An independent 100-decimal directed-interval replay of the exact T139 formulas
at the valid replacement-orbit node `(q,A,N,H)=(1000,666,1000,10000)` gives

```text
B_alpha(1000,666,1000) > 32281.8468558256,
exact FMR digits = {6},
E(D,F) in [-3080140823.433565, -3080140823.433564].
```

Here `D_0<0<F_0`, `D_2>0>F_2`, and `D_6,F_6>0`; the first two opposite-sign
products overwhelm the common-positive product.  Thus positive parent,
decimal recurrence, and even literal FMR do not force `E>0` on a genuine
decimal orbit.  A smaller actual-π node `(q,A,N,H)=(10,5,10,100)` likewise has
positive parent, exact FMR set `{2}`, and directed-interval `E<-3392.514`,
though it lies below the active `k>=3` frontier.  These are finite
`experiments`, not Lean theorems.  They refute only a universal bookkeeping
argument; a π-specific `k>=3` path theorem remains open.

An active-scale replacement now gives a stronger separation. It shares the
T173-certified first 10015 pi digits, has `E>5.889*10^9` at `(1000,334)`, and
follows the legal FMR edge `d=1` to the positive node `(10000,1334)`. There
`{5}` is the complete FMR set but `E<-4.380*10^9`; exactly the child-8
opposite-sign product overwhelms the child-5 common-positive product. The
same replay checks every one of the seven legal root FMR edges: all seven
reached parents are positive and have negative `E`, while each retains exactly
one next FMR child. A shifted base-ten Thue--Morse--Mahler tail preserves every
strict sign on a transcendental `mu=2` orbit (`proof sketch` supported by the
interval `experiment`). Thus even adaptive/existential orbit-generic
cross-energy heredity fails beginning at `q=1000`, without relying on FMR
death. Only a genuinely actual-pi theorem can reopen this proxy. The exact
replay and scope are recorded in the
[pathwise cross-energy separator](../results/negative/20260829-pathwise-cross-energy-heredity-separator.md).

A second independently reproduced directed-interval replacement closes a
broader generic alignment hope.  Take `q=N=1000`, `A=666`, `H=10000`, and let
`alpha=0.overline(w)`, where `w` starts with the same 1000-digit periodic
prefix above and continues with 9000 decimal digits from Python
`Random(191).randrange(10)`.  The exact word pin is

```text
sha256(w)=26f32ba1398b82fd4c537db654f31d364e83ee90169a2fe553886e7ff68a81d1.
```

An independent 100-decimal interval replay certifies

```text
parent B > 32283.1666529341,
exact FMR digits = {1,3},
E < -4435509628.4598,
<x,u> < -7187.1531938592,
||x||^2 > 2546.0588439973,
<x,u>+||x||^2 < -4641.0943498618.
```

Since `||x||^2>0`, this genuine decimal orbit violates
`<x,u>>=-c*||x||^2` for every `c<=1`, despite positive parent and literal FMR.
Thus no universal Gram, projection, positive-definite, or nested-kernel
argument of that alignment form follows from T139/T179 bookkeeping.  The
claim remains a finite `experiment`; it does not touch an additional
actual-π/path-specific hypothesis.

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
