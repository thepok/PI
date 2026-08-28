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
