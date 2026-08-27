# Independent audit: BBP rational-phase density separator

Audit date: **2026-08-13 UTC**

Canonical target: [problems/local/pi-digits.txt](../../problems/local/pi-digits.txt),
SHA-256
`2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825`.
The immutable target is a local, human-authored question and has no external
source URL; none is invented here.

Audited fresh freeze:

- [bbp_rational_phase_density_separator_20260813.md](bbp_rational_phase_density_separator_20260813.md),
  SHA-256
  `1fa0054d89852630c573ad9eee5bd5ae59a442b34809343f7ca9bb7dc1fbc198`;
- [bbp_rational_phase_density_separator_20260813_check.py](bbp_rational_phase_density_separator_20260813_check.py),
  SHA-256
  `72dfd913b3532bfe41e1df9a87ebbb3000f6fe1d179af4edbc0163d2a36cc3bc`.

Independent replay:

- [bbp_rational_phase_density_separator_20260813_independent_check.py](bbp_rational_phase_density_separator_20260813_independent_check.py),
  SHA-256
  `2d55e4abb1a92860a44798c07c970ea2831c33f98ff056ae721cae11f3386ea2`.

## Freeze correction record

The initially assigned report pin was
`1cf301143a585dbcf7abb1a62d54f045869fe98374c7dd7f837cdb14fa3d2169`.
It was superseded before this audit was complete.  The old bytes were no
longer available in the shared workspace, so this audit does **not** assert
that the byte difference was merely editorial.  The independent checker first
rejected its stale pin, was repinned to `1fa0054d...`, and the complete report
was then reread and rederived as a fresh freeze.

## Verdict

**PASS, with two nonfatal scope notes.**

The exact-denominator pointwise separator and the coherent density-one-exact
separator both rederive.  The first has, at every sufficiently large depth,
the exact reduced BBP phase denominator, the exact raw-numerator two-adic
order, positive exponentially accurate forcing, and zero carries.  The second
uses exact BBP forcing outside an exponentially sparse reset set, has
denominator dividing the raw BBP denominator everywhere, and again has zero
carries.  The exponent arithmetic and the Jacobsthal application are correct.

The two scope notes are:

1. The primary finite checker uses doubling resets `(12, 24, 48, 96)`, whereas
   the report says to choose a power-of-two initial reset.  This does not test
   that literal finite wording, although the proof works for any sufficiently
   large initial reset.  The independent checker closes the test-scope gap
   with `(16, 32, 64, 128)`.
2. The report's broad summaries about “exact two-adic order ... and even
   density-one exactness” and about all fixed-difference averaging arguments
   must be read as method-separator statements.  The pointwise sequence has
   the exact denominator/order property; the coherent sequence has the
   density-one exact-forcing property.  The report does not construct one
   sequence having both packages simultaneously, and it does not rule out an
   exact selected-numerator identity.  Sections 3, 4, and the final handoff
   make this narrower scope explicit.

All asymptotic deductions remain a `proof sketch`; finite computation remains
an `experiment`; and inherited dated source checks remain
`literature-checked`.  Nothing is `machine-checked`, a `candidate resolution`,
or a `verified resolution`.  Positive carry density and canonical V1 remain a
`conjecture`.

## 1. Exact forcing and the unique bounded zero-carry orbit

Fix $P\geq1$, put $q=10^P-1$, and write

\[
 a(k)={120k^2+151k+47\over
 (2k+1)(4k+3)(8k+1)(8k+5)},\qquad
 B_m=\sum_{k=0}^m{a(k)\over16^k}.
\]

For

\[
 x_n=q10^nB_{7n},\qquad
 \delta_n=q10^{n+1}(B_{7n+7}-B_{7n}),
\]

direct subtraction gives $x_{n+1}=10x_n+\delta_n$, with
$\delta_n>0$.  If $e_n=x_n-z_n\in[-1/2,1/2)$, then

\[
 e_{n+1}=10e_n+\delta_n-\gamma_n,
 \qquad \gamma_n=z_{n+1}-10z_n.
\]

The exact all-zero-carry solution is

\[
 t_n=-q10^n(\pi-B_{7n}).                              \tag{A1}
\]

Indeed, BBP-tail telescoping gives

\[
 t_{n+1}-10t_n=q10^{n+1}(B_{7n+7}-B_{7n})=\delta_n.  \tag{A2}
\]

It is negative, tends to zero, and is irrational.  If $u_n$ is any other
solution of (A2), then $u_n-t_n=c10^n$; boundedness forces $c=0$.
Therefore the bounded all-zero orbit is unique.  In particular, a rational
bounded zero-carry orbit cannot use the exact forcing forever.  This proves
only that it must reset infinitely often, not that the reset set has positive
density.

The leading constants also check independently.  Since

\[
 a(k)={15\over64k^2}+O(k^{-3}),\qquad
 \sum_{r\geq1}16^{-r}={1\over15},
\]

the tail at $7n$ has leading coefficient
$(15/(64\cdot49))(1/15)=1/3136$.  With
$\lambda=10/16^7=5/2^{27}$, this yields

\[
 t_n=-{q\over3136}\lambda^n n^{-2}(1+O(n^{-1})).     \tag{A3}
\]

Using instead
$\sum_{r=1}^7 16^{-r}=(1-16^{-7})/15$ gives

\[
 \delta_n={q(10-\lambda)\over3136}
           \lambda^n n^{-2}(1+O(n^{-1})).            \tag{A4}
\]

Thus the forcing decay rate is

\[
 b=27\log2-\log5.                                    \tag{A5}
\]

## 2. Reduced-denominator ledger

Let $Q_n$ be the reduced denominator of $q10^nB_{7n}$.  The pinned
all-depth two-adic result and odd-denominator result give, at $m=7n$,

\[
 v_2(\operatorname{den}B_{7n})=28n-v_2(7n+1),
 \qquad \log R_{7n}=(42+o(1))n.                      \tag{A6}
\]

Because $q$ is odd, multiplication by $10^n=2^n5^n$ removes exactly
$n$ powers of two.  Multiplication by fixed $q$ can remove only
$O_P(1)$ odd logarithmic mass.  The exponent of 5 in the raw LCM is
$O(\log n)$, so the possible $5^n$ cancellation also changes the odd
logarithm by only $O(\log n)$.  Consequently

\[
 v_2(Q_n)=27n-v_2(7n+1),\qquad
 \log Q_n=(42+27\log2+o(1))n.                        \tag{A7}
\]

All prime divisors come from the fixed $q$ or from linear factors of size
$O(n)$, so the inherited prime-support estimate gives

\[
 \omega(Q_n)=o(n).                                   \tag{A8}
\]

These statements are for each fixed $P$; no uniformity in growing $P$ is
claimed or needed.

## 3. Pointwise exact-denominator separator

Use the Jacobsthal convention in which $j(M)$ is the least length such that
every interval of $j(M)$ consecutive integers contains an integer coprime
to $M$.  The pinned source audit records Kanold's Satz 4 as

\[
 j(M)\leq2^{\omega(M)}.                              \tag{A9}
\]

The official bibliographic record is H.-J. Kanold, *Über eine zahlentheoretische
Funktion von Jacobsthal*, Math. Ann. 170 (1967), 314--326
([EUDML record](https://eudml.org/doc/161543)).  This audit relies on the
frozen source audit for the theorem text and does not claim a new source
refetch.  Coprimality depends only on the radical, so (A9) applies to $Q_n$
with prime powers unchanged.  The independent checker also directly verifies
this convention for every modulus $2\leq M\leq512$.

Apply (A9) beside the real target $Q_nt_n$.  There is an integer $A_n$
such that

\[
 (A_n,Q_n)=1,\qquad
 \left|{A_n\over Q_n}-t_n\right|
 \leq {2^{\omega(Q_n)}+1\over Q_n}
 =\exp(-(42+27\log2-o(1))n).                         \tag{A10}
\]

Define

\[
 \widetilde e_n={A_n\over Q_n},\qquad
 \eta_n=\widetilde e_n-t_n.
\]

The exponent in (A10) is strictly larger than the decay exponent (A5) of
$|t_n|$.  Hence, for all sufficiently large $n$,
$-1/2<\widetilde e_n<0$; zero is its nearest integer.  Every carry of this
phase sequence is therefore zero.

Its forcing is

\[
 \widetilde\delta_n=\widetilde e_{n+1}-10\widetilde e_n
 =\delta_n+\eta_{n+1}-10\eta_n.                      \tag{A11}
\]

Combining (A4), (A5), and (A10) gives

\[
 {\widetilde\delta_n\over\delta_n}
 =1+O\!\left(\exp(-(42+\log5-o(1))n)\right),         \tag{A12}
\]

because

\[
 (42+27\log2)-(27\log2-\log5)=42+\log5.             \tag{A13}
\]

In particular, $\widetilde\delta_n>0$ eventually.

Now put $D_n=2^{27n}L_{7n}$ and
$\widetilde S_n=D_n\widetilde e_n$.  Since $Q_n\mid D_n$, this is an
integer.  The even $Q_n$ and $(A_n,Q_n)=1$ imply that $A_n$ is odd, so
(A7) gives the exact raw-numerator order

\[
 v_2(\widetilde S_n)
 =v_2(D_n)-v_2(Q_n)=v_2(7n+1).                       \tag{A14}
\]

Finally, $D_n\mid D_{n+1}$ and (A11) imply the exact integer recurrence

\[
 \widetilde S_{n+1}
 =10{D_{n+1}\over D_n}\widetilde S_n
  +D_{n+1}\widetilde\delta_n.                        \tag{A15}
\]

Thus denominator scale alone, even with exact denominator and two-adic order,
does not force a nonzero carry.

## 4. Coherent density-one exact forcing

Choose a sufficiently large power of two $N_0$, set $N_j=2^jN_0$, and at
each $N_j$ choose the pointwise phase above.  On the doubled block
$N_j\leq n<N_{j+1}$, define

\[
 \overline e_n=t_n+10^{n-N_j}\eta_{N_j}.             \tag{A16}
\]

At $n=N_j$ this is the chosen rational.  Equation (A2) then proves by
induction that, before the next reset,

\[
 \overline e_{n+1}=10\overline e_n+\delta_n.         \tag{A17}
\]

Thus every phase is rational despite the representation (A16).  Since the raw
denominators are nested and $D_{n+1}\delta_n$ is integral, the reduced
denominator of $\overline e_n$ divides $D_n$.

The largest amplified reset error in a doubled block is bounded by

\[
 \exp(-(42+27\log2-\log10-o(1))N_j)=o(1).            \tag{A18}
\]

Together with $t_n\to0$, this keeps every phase in $(-1/2,1/2)$ after
increasing $N_0$.  Choosing zero as every nearest integer makes every carry
zero.

The coherent forcing equals $\delta_n$ except immediately before a reset.
At $n=N_{j+1}-1=2N_j-1$, its error is exactly

\[
 \eta_{N_{j+1}}-10^{N_{j+1}-N_j}\eta_{N_j}.          \tag{A19}
\]

There are $O(\log N)$ such indices below $N$, hence their complement has
density one.  Comparing (A19) to (A4) at $n=2N_j-1$ gives relative decay

\[
 \exp(-(c_0-o(1))n),\qquad
 c_0={42+27\log2-\log10\over2}-(27\log2-\log5)
 =21-14\log2+{\log5\over2}>12.1.                    \tag{A20}
\]

So even the exceptional forcing is eventually positive and exponentially
relative-close.  The uniqueness argument in Section 1 also proves that the
resets cannot terminate: a final exact-forcing tail would have to be the
irrational orbit $t_n$.

## 5. Height-product and fixed-difference scope

For an actual rational-shadow zero-carry block beginning at $n_i$, its
nonzero centered phase has reduced denominator $Q_{n_i}$, hence
$|e_{n_i}|\geq Q_{n_i}^{-1}$.  Iterating a length-$h_i$ zero block and
bounding the remaining positive BBP tail gives the report's upper bound

\[
 |e_{n_i}|\leq {1\over2\,10^{h_i}}
 +{q5^{n_i}\over2^{27n_i}15(7n_i+1)^2}.              \tag{A21}
\]

The inherited bound $\mu(\pi)<888/125$ permits only
$h_i\leq(763/125)n_i+O_P(1)$ eventually.  This slope is smaller than
$(27\log2-\log5)/\log10\approx7.429$, so the tail term in (A21) is then
smaller than the first term.  Multiplication over $K$ disjoint blocks
therefore provides
only

\[
 (\log10)\sum_i h_i
 \leq(42+27\log2+o(1))\sum_i n_i+O_P(K).             \tag{A22}
\]

If the blocks cover $N-o(N)$ indices but their count is $K=o(N)$, the
right side may still be $O(KN)$.  Moving every phase to the common nested
denominator $D_N$ gives a product lower bound of order $D_N^{-K}$, not
$D_N^{-1}$.  Likewise

\[
 \prod_i(q10^{n_i}X-z_{n_i})
\]

has degree $K$ and logarithmic height
$O_P(K+\sum_i n_i)$.  This confirms the stated loss in the direct product
ledger.  It does not exclude a new exact identity that produces a shared
small-height factor.

A fixed number of shifts or finite differences enlarges the coherent reset
set by only a fixed-radius neighborhood, still $O(\log N)$, and fixed shifts
preserve the exponential relative scale in (A20).  This is a valid separator
against arguments invariant under those local summaries.  It is not a
theorem excluding arguments that inspect the exact selected numerator
$J_{n,P}=q5^{n+1}H_n$; the report correctly identifies that correlation as
the surviving bottleneck.

## 6. Independent exact replay

The independent checker imports no primary code.  It pins the fresh report,
the primary checker, the canonical target, the frozen recurrence and
denominator audits, the prior Jacobsthal source audit, and the BBP source PDF.
It then runs the primary checker and independently rebuilds the rational BBP
endpoints.

Its deliberately different bounded test scope is:

- periods $P=1,3,5$, instead of the primary $1,2,4$;
- depths $14\leq n\leq140$, instead of $10\leq n\leq128$;
- tail proxies ending at $B_{35n}$, instead of $B_{28n}$; and
- literal power-of-two resets (16,32,64,128), giving exceptional transitions
  (31,63,127).

For each period it checks 127 pointwise states and 126 zero carries.  It
checks 125 coherent states, 124 coherent zero carries, 121 exact-forcing
transitions, and exactly the three reset exceptions.  All exceptional
forcings are positive; the largest observed exceptional relative error has
base-10 logarithm below $-161$.  It also checks every modulus from 2 through
512 against the Jacobsthal convention in (A9), and verifies both exponent
identities numerically.  All structural calculations use integers and
`Fraction`; logarithms are used only for reported diagnostics and the simple
real exponent identities.

Replay from the repository root:

```bash
.venv/bin/python -m py_compile \
  work/ultrapi-resume/bbp_rational_phase_density_separator_20260813_independent_check.py
.venv/bin/python \
  work/ultrapi-resume/bbp_rational_phase_density_separator_20260813_independent_check.py
```

The retained result is `status: PASS`, with
`asserts_positive_carry_density: false` and `asserts_v1: false`.  This finite
replay has status `experiment`; it is not evidence for an infinite density
claim.

## Coordination record

This audit registered the descendant-area watch
`watch:ultrapi:rational-phase-density-separator-audit-20260813` on
`local:pi-digits` for agent
`codex-ultrapi-rational-phase-separator-audit`.  The initial poll was empty at
cursor 56,890.  The final poll delivered sequences 56,898 and 56,906--56,909;
the last processed event, sequence 56,909, was acknowledged.  Sequence 56,898
recorded the primary author's metadata describing the refreeze as restored
TeX delimiters, but observation events are coordination signals only.  It was
not used to infer byte equivalence or to replace the fresh mathematical audit
recorded above.  The later sibling colored-carry events were likewise not
imported as claims or evidence here.

## Claim boundary and handoff

This audit establishes a sound `proof sketch` method separator, not a proof
that any prescribed decimal word occurs in pi.  It proves that the exact BBP
forcing and rationality exclude an eventual all-zero-carry tail, but it also
shows why that infinitude statement cannot be upgraded to positive carry
density using only denominator height, the displayed two-adic order,
positivity, finite asymptotic data, or density-one forcing agreement.

The exact selected-numerator correlation at every depth remains uncontrolled.
No positive lower density of nonzero carries is proved, and canonical V1
remains a `conjecture`.
