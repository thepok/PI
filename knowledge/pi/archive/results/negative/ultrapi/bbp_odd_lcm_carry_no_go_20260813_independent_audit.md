# Odd-LCM BBP carry no-go: independent adversarial audit

Audit date: **2026-08-13 UTC**.

Canonical target: [problems/local/pi-digits.txt](../../problems/local/pi-digits.txt),
SHA-256
`2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825`.
The target is Marcel's immutable local question and has no external source URL.

Frozen primary artifacts:

- [bbp_odd_lcm_carry_no_go_20260813.md](bbp_odd_lcm_carry_no_go_20260813.md),
  SHA-256
  `fcea6cb14082ee404fabf14a68215a3b7394d553ed401e51e8f70a333f234bfc`;
- [bbp_odd_lcm_carry_no_go_20260813_check.py](bbp_odd_lcm_carry_no_go_20260813_check.py),
  SHA-256
  `12d9ffef815f60b39d8f4d2f8c946bab10c1e29be94d25f19dfb1039ee15a905`.

Independent replay:
[bbp_odd_lcm_carry_no_go_20260813_independent_check.py](bbp_odd_lcm_carry_no_go_20260813_independent_check.py),
SHA-256
`0af6a02596bafec6253338e788b1b44d29bb1235511e9f8ac267c5b8eb3b484d`.

## Verdict

**PASS — the infinite deductions are a sound `proof sketch`, and the finite
replay is an `experiment`.**

The quantifiers in the V1 implication, the exact torsion-neighborhood
threshold, the transfer to the eventually equal rational carries, the formula
for $h_P(n)$, and both restricted-denominator equivalences are correct. The
odd-LCM congruence is genuinely carry-blind and the five-row finite
falsification replays exactly.

This report proves no positive carry density and no decimal-word occurrence
for pi. Canonical V1 remains a `conjecture`. Nothing audited here is
`machine-checked`, a `candidate resolution`, or a `verified resolution`.

## Freeze correction

The initially assigned report hash
`24b48a1056b2c202532ad959b4f5d86088e01c19f7e2fad4f25d511c98d16465`
was stale after a notation cleanup. The coordinator explicitly refroze the
observed report at
`fcea6cb14082ee404fabf14a68215a3b7394d553ed401e51e8f70a333f234bfc`
while retaining the checker hash above. This audit rejected the stale pin and
used only the refrozen pair. Neither frozen file was edited during this audit.

## 1. Quantifiers and the V1 implication

Fix $P\geq1$ first and put $q=10^P-1$. For arbitrary $H\geq1$ and
$N\geq0$, the claimed implication is

\[
 \mathrm{V1}\Longrightarrow
 \exists n\geq N:\quad
 \gamma_{n,P}=\gamma_{n+1,P}=\cdots=
 \gamma_{n+H-1,P}=0.                              \tag{A}
\]

The proof has no hidden uniformity in $P$: the eventual BBP-agreement onset
may depend on the fixed $P$. The order is

\[
 \forall P\geq1\ \forall H\geq1\ \forall N\geq0\ \exists n\geq N,
\]

not one $n$ or one onset shared by all periods.

V1 makes the decimal orbit
$\mathcal O=\{10^n\pi\bmod1:n\geq0\}$ dense. Every decimal cylinder is
visited, leading-zero cylinders are included, and every nonempty open circle
arc contains a smaller decimal cylinder. Irrationality of pi prevents an
orbit point from lying on a terminating-decimal endpoint.

Every tail is also dense. With $T(x)=10x\bmod1$,

\[
 T^N(\overline{\mathcal O})=\mathbb T
 \subseteq \overline{T^N(\mathcal O)},
\]

because $T^N$ is continuous and surjective. Multiplication by the fixed
integer $q$ is likewise continuous and surjective, so every tail of
$\{q10^n\pi\bmod1\}$ is dense. This proves the required arbitrarily late
returns to the zero neighborhood.

## 2. Exact zero-block and q-torsion thresholds

Let

\[
 z_n=\left\lfloor q10^n\pi+\tfrac12\right\rfloor,
 \qquad e_n=q10^n\pi-z_n,
 \qquad \gamma_n=z_{n+1}-10z_n.
\]

Since pi is irrational, $-1/2<e_n<1/2$ with no tie. Iterating
$e_{n+1}=10e_n-\gamma_n$ gives the exact equivalence

\[
 \gamma_n=\cdots=\gamma_{n+H-1}=0
 \iff |e_n|<\frac1{2\,10^H}
 \iff \|q10^n\pi\|_{\mathbb T}<\frac1{2\,10^H}.   \tag{B}
\]

For the converse, the strict bound keeps $10^t e_n$ in the same open
nearest-integer cell for every $0\leq t\leq H$, hence
$z_{n+t}=10^t z_n$. Thus the report neither loses a factor of ten nor uses
the wrong boundary orientation.

The qualitative torsion statement has the following exact scale. If

\[
 K_q=\{k/q\bmod1:0\leq k<q\},
\]

then for every circle point $x$,

\[
 \|qx\|_{\mathbb T}=q\,\operatorname{dist}_{\mathbb T}(x,K_q). \tag{C}
\]

Consequently the right side of (B) is exactly

\[
 \operatorname{dist}_{\mathbb T}(10^n\pi,K_q)
 <\frac1{2q10^H}.                                  \tag{D}
\]

Closeness to zero is one sufficient torsion neighborhood, but any of the
$q$ torsion points works. The independent checker brute-forces (C) on 239
exact rational circle points for $q=9,99,999$ and checks 1,434 exact instances
of the threshold equivalence (D).

Combining tail density with (B), after replacing $N$ by the maximum of $N$
and the fixed-$P$ agreement onset, proves (A) for the true carries and for the
sevenfold rational carries. Equality of rational and true nearest integers at
all sufficiently large indices gives equality of their consecutive carries;
no onset uniform in $P$ is asserted or needed.

Therefore a uniform bounded gap between nonzero carries would contradict V1.
This does not contradict positive lower density: a positive-density set may
have complementary intervals of unbounded length.

## 3. Exact formula for the maximal zero run

Let $h_P(n)\geq0$ be the maximal number of consecutive zero carries beginning
at $n$. An infinite run would force $e_n=0$ and hence make pi rational, so the
maximum is finite. Put

\[
 x_n=-\log_{10}\bigl(2\|q10^n\pi\|_{\mathbb T}\bigr)>0.
\]

By (B), a block of integer length $H$ exists exactly when $H<x_n$. If
$x_n$ were an integer $H$, then
$\|q10^n\pi\|_{\mathbb T}=1/(2\,10^H)$, which would express pi as a rational
number. Hence $x_n\notin\mathbb Z$ and

\[
 h_P(n)=\lfloor x_n\rfloor.                        \tag{E}
\]

The nonintegrality is essential: without it, the strict inequality in (B)
would give $h_P(n)=x_n-1$ at an integral boundary. The report explicitly
excludes that boundary using irrationality, so its floor formula is correct,
including the case $h_P(n)=0$.

The independent checker tests 1,152 exact nonboundary rational states,
constructs their carries directly, and compares the observed first nonzero
carry with the log-free form of (E). It also checks 6,912 finite versions of
(B). These bounded rows have label `experiment`.

## 4. Logarithmic bounds and restricted exponent one

Equation (E) gives the exact sandwich

\[
 \frac1{2\,10^{h_P(n)+1}}
 <\|q10^n\pi\|_{\mathbb T}
 <\frac1{2\,10^{h_P(n)}}.                          \tag{F}
\]

For fixed $P$, (F) proves, after changing positive constants in either
direction,

\[
 h_P(n)=O(\log(n+2))
 \iff
 \|q10^n\pi\|_{\mathbb T}\geq c(n+2)^{-C}.        \tag{G}
\]

This is the precise meaning of the report's equivalence between (24) and
(25). Strict versus non-strict inequalities are absorbed by the constants;
the exponent and additive constant are not claimed to remain numerically
identical in both directions.

With the prescribed, generally unreduced denominator $Q_n=q10^n$ and nearest
integer $z_n$,

\[
 \left|\pi-\frac{z_n}{Q_n}\right|
 =\frac{\|q10^n\pi\|_{\mathbb T}}{Q_n}.            \tag{H}
\]

Thus (G) is a $Q_n^{-1}$ lower bound with a power of
$n\asymp\log Q_n$ as loss. It is a statement only about this restricted
denominator grid; it is not the global irrationality exponent and does not
require $z_n/Q_n$ to be reduced. The independent checker confirms (H) on
1,152 exact rows.

Moreover, $0\leq x_n-h_P(n)<1$, while

\[
 -\log_{10}\|q10^n\pi\|_{\mathbb T}=x_n+\log_{10}2.
\]

The bounded difference proves

\[
 h_P(n)=o(n)
 \iff
 -\log_{10}\|q10^n\pi\|_{\mathbb T}=o(n).         \tag{I}
\]

Indeed the approximation exponent measured on the prescribed grid is

\[
 \frac{-\log_{10}|\pi-z_n/Q_n|}{\log_{10}Q_n}
 =1+\frac{-\log_{10}\|q10^n\pi\|_{\mathbb T}}
          {n+\log_{10}q},                          \tag{J}
\]

so (I) is exactly exponent one along this grid. The report correctly does not
upgrade this to an all-denominator statement.

## 5. Irrationality-measure and rational-agreement limits

The parent report and its independent audit are pinned at hashes
`bdc77060ef42a15f8985d70b70cf9777c36070713c940a18e89e05b149734d55`
and
`ae7e6c84ca6ec253107c2fa48ed202c5ef4f3aadbee75cbd1bca3d2d03dafe91`.
They establish the source applicability and fixed-$P$ quantifiers used here.

For $M=888/125$, the restricted nearest approximant satisfies eventually

\[
 \|q10^n\pi\|_{\mathbb T}>(q10^n)^{1-M},
\]

which yields only

\[
 h_P(n)<\frac{763}{125}n
 +\frac{763}{125}\log_{10}q-\log_{10}2.
\]

The slope arithmetic is exact. A finite global irrationality measure therefore
gives an $O_P(n)$ gap bound, not (G) or (I).

For the sevenfold rational shadow, the ratio of its BBP-tail bound to the
nearest-boundary lower bound is

\[
 \frac{2^8q^8}{15(7n+1)^2}
 \left(\frac{10^8}{16^7}\right)^n,
 \qquad \frac{10^8}{16^7}=\frac{390625}{1048576}<1. \tag{K}
\]

For each fixed $q$, (K) tends to zero. The independent checker obtains exact
comparison onsets 12, 30, 66, and 139 for $P=1,2,4,8$, respectively. These
are only onsets for the numerical comparison (K); actual rational agreement
also waits for the source-level irrationality-measure onset. The report makes
only the correct eventual fixed-$P$ claim.

## 6. Odd-LCM recurrence and finite falsification

The primary checker was rerun independently and returned `PASS`. It reconstructs
800 sevenfold BBP transitions, checks 8,800 congruences after replacing the
actual carry by each candidate in $\{-5,\ldots,5\}$, factors all five displayed
LCM quotients, checks unit forcing, and certifies the true six-zero window from
the pinned decimal enclosure.

The algebraic reason is exact: both $10\alpha_nS_n$ and every candidate
carry multiple $cD_{n+1}$ vanish modulo $R_n$, leaving
$S_{n+1}\equiv J_n\pmod{R_n}$. Thus this congruence cannot distinguish the
actual carry. The five zero-carry rows with nontrivial squarefree $R_n$ and
$\gcd(J_n,R_n)=1$ are an `experiment` that falsifies the proposed local
fresh-prime rule; they prove no asymptotic frequency statement.

## Coordination record

The audit registered the descendant-area watch
`watch:ultrapi:odd-lcm-independent-audit-20260813` on `local:pi-digits` for
agent `codex-ultrapi-odd-lcm-audit`. The initial and final polls were empty at
cursor and delivered sequence 56,880, so there was no event to acknowledge.
This observation is coordination state only and is not mathematical evidence.

## Replay and claim boundary

Run from the repository root:

```bash
.venv/bin/python -m py_compile \
  work/ultrapi-resume/bbp_odd_lcm_carry_no_go_20260813_independent_check.py
.venv/bin/python \
  work/ultrapi-resume/bbp_odd_lcm_carry_no_go_20260813_independent_check.py
```

The retained run reports `status: PASS`, pins all seven inputs, and explicitly
sets the bounded-gap, logarithmic-gap, positive-density, and V1 assertion
flags to false. No formal code was changed, so this branch makes no
`machine-checked` claim and requires no axiom-audit registration.

The useful conclusion is a no-go boundary, not a solution: V1 would itself
produce arbitrarily late fixed-$P$ zero-carry blocks, fresh odd-LCM valuations
cannot see the carry, and known irrationality bounds stop at a linear gap
scale. The missing target remains an average, pi-specific positive-density
argument. Canonical V1 remains a `conjecture`.
