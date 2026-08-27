# Transfer-compatible directional kernel

Status: `proof sketch`

This note records an independently audited algebraic reduction. It does not
prove a fixed-π estimate, occurrence of any prescribed word, density,
normality, V1, or novelty.

## Transfer-compatible family

Let

\[
\Phi_q(t)=\frac1{q^2}\left|\sum_{r=0}^{q-1}e^{2\pi i r t}\right|^2
\]

and define

\[
H_{q,c}(t)=2\Phi_q(t)^2-c\bigl(1-\cos(2\pi q t)\bigr)\Phi_q(t).
\]

The old normalized Jackson minorant is (H_{q,1}); the normalized
boundary-matched minorant is (H_{q,c_q^\sharp}) with (c_q^\sharp) below.
It has Fourier support in \(|h|\le 2q-1\), total signed coefficient mass
\(H_{q,c}(0)=2\), and zero coefficient

\[
\mu_q(c)=\int_0^1H_{q,c}(t)\,dt
=\frac{4q^2+2}{3q^3}-\frac cq.
\]

For an integer base \(b\ge2\), put

\[
(L_bf)(z)=\sum_{d=0}^{b-1}f\!\left(\frac{z+d}{b}\right).
\]

Writing \(q=bm\), exact conservation

\[
L_bH_{bm,c_{bm}}=H_{m,c_m}
\]

holds precisely when

\[
c_m-c_{bm}=\frac{2(b^2-1)}{3b^2m^2}.
\]

Across a multiplicatively closed scale system, the solutions are exactly

\[
c_q=C+\frac{2}{3q^2}.
\]

Thus, with \(M_{q,C}=H_{q,\,C+2/(3q^2)}\), one has the exact preimage identity

\[
\boxed{\sum_{d=0}^{b-1}M_{bm,C}\!\left(\frac{z+d}{b}\right)=M_{m,C}(z).}
\]

The centered-cylinder sign condition requires

\[
c_q\ge c_q^\sharp=\frac{2}{q^2(1-\cos(\pi/q))}.
\]

For all scales \(q\ge2\), the least compatible constant is

\[
\boxed{C_*=\frac4{\pi^2}}.
\]

Accordingly, the distinguished transfer-compatible minorant is

\[
M_q=H_{q,\,4/\pi^2+2/(3q^2)}.
\]

The classification and the optimality of \(C_*\) are algebraic/analytic
claims at `proof sketch` status here; they are not part of the Lean trust
boundary.

## Branch innovation

For \(q=bm\), set

\[
y_d=\frac{z+d}{b},\qquad p_d(z)=\Phi_b(y_d),\qquad
R_b(z)=\sum_{j=0}^{b-1}p_j(z)^2,
\]

so \(\sum_dp_d=1\). The transfer-compatible kernel has the pointwise branch
decomposition

\[
\boxed{M_{bm,C}(y_d)
=p_d(z)M_{m,C}(z)
+2p_d(z)\bigl(p_d(z)-R_b(z)\bigr)\Phi_m(z)^2.}
\]

The innovation terms sum to zero over \(d\). At decimal scales this is a
target-digit-sensitive recurrence: the branch weight depends on the actual
predecessor digit and the suffix-centered successor phase. Equal-child
averaging preserves the parent score but discards exactly the information
needed for a prescribed leading digit.

## Narrow no-go

There are pointwise configurations with positive parent score, one positive
child, and each of the other nine children negative (after an arbitrarily
small perturbation away from the Fejér zeros). Hence parent positivity,
preimage conservation, total signed mass, or the equal average over children
can imply at most that *some* child is positive. They cannot imply positivity
for *every prescribed* child.

This does **not** rule out target-branch estimates, vector- or matrix-valued
transfer states, stopping-time arguments, or π-specific arithmetic control.
It retires only the parent-only bootstrap

```text
positive suffix score  =>  all leading-digit extensions are positive.
```

The remaining input is branch-sensitive signed control, equivalently control
of predecessor digits conditioned on the suffix phase.
