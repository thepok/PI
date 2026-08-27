# T117 normalized residue and occupancy direction audit

Status: `proof sketch`

Date: 2026-08-22 UTC

Prompt SHA-256:
`e92aed4545a51de395c632a73f715173cdae6af24767b9a3785a9a1cc775feba`

Response SHA-256:
`247041512d1d441cd34033bba90c914bb7d51733e8a40e53feaa7c80f8004eed`

This report retains the independently reviewed mathematical deductions from a
ChatGPT Pro direction audit. T117's decomposition is now separately
`machine-checked` in the canonical Lean core; the counterexamples and
collision-energy deductions below remain `proof sketch`. The proposed finite
diagnostic is an `experiment` design and has not been run here.

## Generic denominator claims that are closed

Use T117's notation

\[
H=\gcd(D,E),\quad d=D/H,\quad e=E/H,
\quad X=10Ae+Cd,\quad k=\gcd(X,Hd).
\]

The candidate inequality `k^2 ≤ e` is false under only the generic reduced-pair
hypotheses. Take

\[
(A,C,D,E)=(1,1,2,1).
\]

Both pairs are reduced, but `H=1`, `d=2`, `e=1`, `X=12`, and `k=2`, so
`k^2=4>1=e`. Any proof of this inequality along the actual sampled-BBP orbit
must therefore use additional BBP-specific structure.

Even `k^2 ≤ e` together with an unbounded reduced successor denominator does
not generically imply cell motion. For any positive `t`, take

\[
(A,C,D,E)=(0,1,1,t).
\]

Then `H=d=k=X=1`, `e=t`, and the reduced successor is `1/t`. For every fixed
mesh `q` and every `t>q`, its cell is zero. Thus denominator growth alone
cannot yield prescribed-cell occupancy.

These examples do not refute an actual-orbit inequality. They close only a
generic deduction from reduced-pair algebra and any denominator-only route to
cell motion.

## Collision-energy target

For an actual positive-denominator successor define

\[
a_N=X_N/k_N,\qquad b_N=D_Ne_N/k_N,\qquad
r_N=a_N\bmod b_N,
\]

and, for a mesh `q`,

\[
c_{q,N}=\left\lfloor q r_N/b_N\right\rfloor.
\]

On a finite index window `W` of length `L`, let

\[
n_c=\#\{N\in W:c_{q,N}=c\},\qquad
J_q(W)=\sum_{c=0}^{q-1}n_c^2.
\]

If any cell is empty, Cauchy--Schwarz gives the exact obstruction

\[
J_q(W)\ge L^2/(q-1).
\]

Consequently, an actual-orbit estimate

\[
J_q(W)\le L^2/q+B_qL
\]

forces every cell to occur whenever `L > B_q q(q-1)`. Equivalently, for

\[
S_h(W)=\sum_{N\in W}\exp(2\pi i h c_{q,N}/q),
\]

finite Fourier orthogonality gives

\[
J_q(W)=\frac1q\left(L^2+\sum_{h=1}^{q-1}|S_h(W)|^2\right),
\]

so the strict bound

\[
\sum_{h=1}^{q-1}|S_h(W)|^2<L^2/(q-1)
\]

is sufficient for full cell occupancy. This is an elementary `proof sketch`,
not an estimate currently known for the sampled-BBP orbit. T111 already
contains a related machine-checked DFT-to-cell interface; the missing input is
actual cross-index cancellation or anti-concentration.

## Preregistered finite diagnostic

Status: `experiment`

If the independently verified normalized T117 census over `N=512,...,4095`
is run, partition it before inspection into fourteen consecutive half-open
windows of length 256. On each window compute the exact `q=10` cells and
`J_10(W)`, and test the fixed local `conjecture`

\[
J_{10}(W)<256^2/9.
\]

Because an omitted cell would force `J_10(W) ≥ 256^2/9`, survival certifies
full ten-cell occupancy only in that finite window. It is not evidence of
arbitrarily-late occupancy, density, normality, V1, or a general theorem.

Stop conditions are frozen as follows:

1. Any mismatch in `U=HX`, `V=H^2de`, `g=Hk`, reducedness, or the independently
   reconstructed cell invalidates the run as an implementation failure.
2. The first actual-orbit witness `k^2>e` terminates the K1 direction; retain
   the least complete exact tuple and independent replay.
3. If any preregistered 256-window fails the strict `J_10` inequality, reject
   this local anti-concentration `conjecture` without moving boundaries or
   tuning the threshold.
4. If every finite test survives through `N=4095`, retain only `experiment`.
   Do not extend the census without a symbolic BBP-specific statement that
   controls `r_N/b_N`, same-cell pairs, a cross-determinant, or an exponential
   sum.
5. Stop a proof route if it only enlarges `b_N`, uses only the generic
   determinant lower bound `|r_nb_m-r_mb_n|≥1`, fails to beat
   `L^2/(q-1)`, or leaves the accumulated numerator uncontrolled.

## Direction decision

Retain T117 as exact coordinates and complete one final pointwise Lean bridge
from `X/k mod b_N` to the endpoint-exact cell interval. After that,
denominator-only and representation-only work stops. The next substantive
research direction is an actual sampled-BBP numerator anti-concentration,
same-cell pair bound, or signed-DFT estimate across indices.

No verified resolution or unconditional digit-occurrence result is claimed.
