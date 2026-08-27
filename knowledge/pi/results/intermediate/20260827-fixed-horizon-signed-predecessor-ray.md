# Fixed-horizon signed predecessor ray from the `(1000,334,10000)` seed

Status: `proof sketch` built from one directed-interval `experiment` and the
machine-checked T172 transport. The recurrence and constants were independently
algebra-audited. This is not V1 and is not a natural-horizon theorem beyond the
first child.

Date: 2026-08-27 UTC

## Statement

Put `q_r = 1000 * 10^r` and keep the horizon fixed at `N = 10000`. Starting
from `A_0 = 334`, there are digits `d_r < 10` and coherent left extensions

\[
 A_{r+1}=A_r+d_rq_r,\qquad 0\le A_r<q_r,
\]

such that, for every `r >= 0`,

\[
 \Re Z^\pi_{q_r,A_r}(10000)
 > \frac{71221}{3750\,10^r}
   +\frac7{300\,10^{2r}}>0. \tag{1}
\]

For the first child this gives the concrete bound

\[
 \Re Z^\pi_{10000,A_1}(10000)>\frac{94973}{50000}=1.89946. \tag{2}
\]

Here the target-signed Archimedean information for the actual constant pi
enters only through the replayed seed

\[
 \Re Z^\pi_{1000,334}(10000)>\frac{47539}{2500}.
\]

T172 is generic but preserves that sign along a coherent target ray.

## Derivation

T172 machine-checks that for every `q >= 1000` some `d < 10` satisfies

\[
 \Re Z^\pi_{10q,A+dq}(N)
 \ge \frac{\Re Z^\pi_{q,A}(N)-N\,21/(10q^2)}{10}. \tag{3}
\]

Choose one such digit recursively. Multiplying the `r` successive inequalities
by the appropriate power of ten gives

\[
 10^r\Re Z^\pi_{q_r,A_r}(10000)
 >\frac{47539}{2500}
   -10000\sum_{j=0}^{r-1}
      10^j\frac{21}{10(1000\,10^j)^2}.
\]

The finite geometric sum is

\[
 10000\sum_{j=0}^{r-1}
      10^j\frac{21}{10(1000\,10^j)^2}
 =\frac7{300}(1-10^{-r}).
\]

Since `47539/2500 - 7/300 = 71221/3750`, division by `10^r`
proves (1). Strictness is inherited from the strict seed bound.

T176 now machine-checks the stronger structural packaging for every finite
block `[M,M+L)`. With

\[
 \Psi(q)=\frac7{3q},\qquad
 \mathcal B_{q,A}[M,L]
 =q\Re Z^\pi_{q,A}[M,L]-L\Psi(q),
\]

some child has strictly larger Bellman surplus. The equality
`q*21/(10q^2)=Psi(q)-Psi(10q)` and T172's strict mass bound are exactly what
make the increase strict. This block theorem is `machine-checked`; composing
it with the still-experimental root score leaves the actual-pi ray itself at
`proof sketch` status.

T178 additionally machine-checks the infinite recursive selection itself:
the coherent targets stay below `q_r`, every selected digit is below ten, and
the Bellman surplus strictly increases at each level. Conditional on a
positive root surplus it proves the explicit all-level bound

\[
 \frac{7L}{3q_r^2}<\Re Z^\pi_{q_r,A_r}(L).
\]

Thus no compactness or informal dependent-choice step remains. Only the
actual numerical root premise is outside the Lean trust boundary.

## What is genuinely new

This is an actual-pi, target-signed, coherent family on unbounded decimal
scales. It is stronger than an isolated positive score and stronger than the
generic T172 identity alone: the complete target phase remains present and the
positive lower bound is explicit at every rung.

The result nevertheless does not approach all targets by itself. The selected
digit is existential, so the construction follows one predecessor ray rather
than branching over all ten children.

More decisively, the horizon stays `N=10000`. At `r=1` it equals the natural
scale `q_1=10000`, so (2) feeds the verified T156 hit consumer. For every
`r>1`, however, `N<q_r`; positivity of this fixed-horizon score has no current
occurrence consumer. The ray must not be advertised as an unbounded word-hit
theorem.

## Next atomic rung

The live mathematical gap is now sharply separated from the completed
transport algebra: obtain target-signed control while increasing the horizon
with the scale, or control at least one nonzero predecessor-digit character so
that more than the existential zero-character child survives. Any proposed
lemma must identify the pi-specific source of that new sign; another fixed-`N`
iteration or coefficient identity is not enough.
