# Boundary-kernel carry flow

Status: `proof sketch`

This note records an independently audited transport mechanism and two narrow
no-go results. It proves no fixed-π cancellation estimate, prescribed-word
occurrence, density, normality, V1, or novelty.

## Exact carry decomposition and leakage

Let

\[
K_q(t)=\bigl(\cos(2\pi t)-\cos(\pi/q)\bigr)F_q(t)^2,
\qquad
F_q(t)=\frac1q\left(\frac{\sin(\pi q t)}{\sin(\pi t)}\right)^2.
\]

Write a length-\(k\) target word as \(dv\), where \(d\) is its first digit,
the nonempty suffix \(v\) has scale \(Q=10^{k-1}\), and the child scale is
\(q=10Q\). Thus this renormalization starts at \(k\ge2\), while one-digit
words remain a separate base case.
For the decimal orbit \(x_n=\{10^n\pi\}\), define

\[
a_n=\lfloor10x_n\rfloor,
\quad s_{v,n}=\left\lfloor x_{n+1}-c_v+\frac12\right\rfloor,
\quad y_{v,n}=x_{n+1}-c_v-s_{v,n}\in[-1/2,1/2),
\]

and the carry-corrected predecessor digit

\[
\eta_{v,n}\equiv a_n+s_{v,n}\pmod {10}.
\]

The carry is essential at the transitions
\(d99\ldots9\leftrightarrow(d+1)00\ldots0\). Define the matching parent-scale
observable \(H_Q(y)=K_{10Q}(y/10)\). Then the ten child coordinates satisfy

\[
\bigl(K_{10Q}(x_n-c_{dv})\bigr)_{d=0}^{9}
=H_Q(y_{v,n})e_{\eta_{v,n}}+R_{v,n},
\]

where the matching remainder is zero and, for \(d\ne\eta_{v,n}\),

\[
-\frac{C_{\rm off}}{Q^2}\le R_{v,n,d}\le0,
\qquad C_{\rm off}=\frac1{50\sin^2(\pi/20)}.
\]

Moreover \(H_Q(y)=M_Q(y)K_Q(y)\) for an explicit positive factor \(M_Q\),
so the matching child has the same sign and exact boundary as the suffix-scale
kernel; the other nine channels contribute only \(O(Q^{-2})\) per visit.

## A sufficient incoming-edge criterion

Define the target incoming-edge flow

\[
P_{d\mid v}(N)=\sum_{\substack{n<N\\\eta_{v,n}=d}}H_Q(y_{v,n}).
\]

Summing the pointwise identity gives

\[
\Sigma_{dv}(N)=P_{d\mid v}(N)+E_{d\mid v}(N),
\qquad -\frac{C_{\rm off}N}{Q^2}\le E_{d\mid v}(N)\le0.
\]

Therefore the concrete sufficient condition

\[
\boxed{P_{d\mid v}(N)>\frac{C_{\rm off}N}{Q^2}}
\]

forces \(\Sigma_{dv}(N)>0\), hence a hit of the target cylinder under the
boundary-minorant consumer. No estimate of this form is known for π.

Equivalently, with \(\omega=e^{2\pi i/10}\), the digit projector decomposes
\(P_{d\mid v}\) into transported suffix mass plus nine nontrivial character
correlations of \(\eta_{v,n}\). These nine signed correlations, not another
scalar norm, are the unresolved input.

## Narrow successor-only no-go

For fixed suffix center \(c_v\), the ten preimages

\[
x_a=\frac{a+c_v}{10},\qquad a=0,\ldots,9,
\]

all have the same successor \(10x_a\bmod1=c_v\), but their child vectors are
supported in different coordinates:

\[
\bigl(K_{10Q}(x_a-c_{dv})\bigr)_{d=0}^{9}=K_{10Q}(0)e_a.
\]

Thus the successor state, suffix phase, or any scalar observable of that
successor cannot reconstruct a target-uniform lower bound for all incoming
children. This no-go is only about **successor-only scalar information**. It
does not exclude predecessor-digit state, the nine character channels, or a
π-specific numerator argument.

## Narrow finite 10-ray no-go

For a finite trigonometric polynomial

\[
f(x)=\sum_{h\ne0}b_he(hx),
\]

write every frequency uniquely as \(h=10^ru\), with \(10\nmid u\), and set

\[
p_u=\sum_{r\ge0}b_{10^ru}.
\]

There is an exact decomposition

\[
f=P+g\circ T-g,
\qquad T(x)=10x\bmod1,
\qquad P(x)=\sum_{10\nmid u}p_ue(ux).
\]

Consequently a finite polynomial telescopes to endpoint terms exactly only if
every primitive-ray sum \(p_u\) vanishes. For the centered boundary kernel at
\(q=10^k\), the primitive ray \(u=q+1\) contains only that frequency within
the support \(|h|\le2q-1\); the audited coefficient calculation gives a
nonzero ray sum. Hence this finite centered kernel is not an exact finite
\(T\)-coboundary.

This finite-ray calculation by itself rules out only exact endpoint
telescoping.  The later audited fixed-survivor addendum in
`../negative/20260824-scalar-uniform-coboundary-carry-budget-no-go.md` also
closes state-uniform pointwise scalar subactions, literal-sup approximations,
and infinite expansions convergent at the survivor. Essential-
\(L^\infty\)/almost-everywhere and \(L^p\) statements, general vector or skew
extensions, and arithmetic cancellation special to π remain open.
