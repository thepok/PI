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

Finite π replay supplies a positive root and two surviving levels only. The
inductive theorem needed is along one consistently selected unbounded path;
assuming such reached nodes in advance is circular. After transport, a
separate viable-branching or selector-word coverage argument remains.
