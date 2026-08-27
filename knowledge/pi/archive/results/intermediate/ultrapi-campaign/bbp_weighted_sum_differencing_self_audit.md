# Adversarial self-audit of the BBP weighted-sum obstruction

Audit date: **2026-08-12 UTC**

Target: [`bbp_weighted_sum_differencing_attack.md`](bbp_weighted_sum_differencing_attack.md)

Corrected target SHA-256:
`33fe8e27130e7ed4acfb8b9ee017cb17df2a612a1a4674b5d5ccef88c4404713`

Primary checker SHA-256:
`70a4ca42b1bd2c6ec212587662ab667b8c1940a3a95d94b03a1f054ba71066bc`

Self-audit checker SHA-256:
`39665d0cc03870755e0a3b9f3ab84fb727d128c22bdcd9f51d35804f4b4bf512`

Canonical question SHA-256:
`2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825`

## Verdict and claim labels

**PASS after one boundary correction.**  The first draft chose
$M=\lfloor(N-1)/\lambda\rfloor$ in the block-to-global argument and
misstated the resulting endpoint by one.  The pinned report instead uses
$M=\lceil(N-1)/\lambda\rceil$, for which
$\lfloor\lambda M\rfloor+1\in\{N,N+1\}$.  The geometric blocking proof and
normality conclusion are correct with that repaired endpoint.  No constant,
index, selector condition, or scope statement otherwise changed.

The report's new mathematical results retain label `proof sketch`.  Both
checker outputs are `experiment`; the source applicability search is
`literature-checked`; and the cited pre-existing T13 and T26 declarations
are `machine-checked`.  This is a self-audit, not independent expert review.
No weighted-sum estimate, Fourier limit, fixed return, V1, `candidate
resolution`, or `verified resolution` is claimed.

## 1. Weighted-sum collapse and pi transfer

The parent decomposition is

\[
 16B_M\equiv
 \kappa_M+\frac{\eta_M}{C_M}\pmod1.
\]

Because $A_n=(10^n-16)/16$ is integral throughout the row, multiplication
inside a character gives exactly

\[
 e(hA_n\kappa_M)e(hA_n\eta_M/C_M)
 =e(h(10^n-16)B_M).
\]

There is no dropped CRT factor or representative ambiguity.  The positive
BBP tail obeys

\[
 \pi-B_M
 \le\frac1{(M+1)^2}\sum_{k=M+1}^{\infty}16^{-k}
 =\frac{16^{-M}}{15(M+1)^2}.
\]

For $n\le\lfloor\lambda M\rfloor$, $10^n\le16^M$.  Hence every phase
error is at most $1/[15(M+1)^2]$, and the character chord bound is exactly

\[
 \frac{2\pi|h|}{15(M+1)^2}.
\]

This is already a normalized-average bound; no extra factor $T_M$ belongs
on its right side.  It proves equivalence of the two zero limits along the
same unbounded depth sequence and for each fixed $h$.  It proves neither
limit.

## 2. Audit of the all-depth normality boundary

If global partial sums are $o(N)$, subtracting their values at $M$ and
$L_M+1$ immediately gives $o(M)$ proportional blocks.  Conversely, assume
every proportional block is $o(M)$.  For a large endpoint $N$, let

\[
 M=\left\lceil\frac{N-1}{\lambda}\right\rceil.
\]

Then

\[
 N-1\le\lambda M<N-1+\lambda<N+1,
\]

because $1<\lambda<2$.  Therefore

\[
 \lfloor\lambda M\rfloor+1\in\{N,N+1\}.
\]

The missing or extra endpoint contributes at most one unit summand.  Repeating
with $M=N/\lambda+O(1)$ produces a geometric backward sequence.  Given
$\varepsilon>0$, all sufficiently large block errors are at most
$\varepsilon M$, and their geometric sum is $O_\lambda(\varepsilon N)$;
the finitely many terminal terms are $o(N)$.  Thus every global nonzero
Fourier sum is $o(N)$, and Weyl's criterion gives base-10 normality.

This equivalence requires convergence through **all** depths.  The parent's
condition (43) only requires one common unbounded subsequence and is not
silently promoted to normality.

## 3. Audit of finite differencing

For $f(n)=h(10^n-16)B_M$,

\[
 \Delta_r f(n)=h10^n(10^r-1)B_M.
\]

Induction multiplies by one new $10^s-1$ at every step.  The sign in the
report agrees with the convention $\Delta_r f(n)=f(n+r)-f(n)$.  The first
correlation consequently has promoted frequency $h(10^r-1)$ and the
endpoint range $M\le n\le L_M-r$.

Every promoted factor is odd.  With
$K_M=4M-v_2(M+1)$, the residual two-adic denominator exponent at a base
index $n\le L_M$ is

\[
 K_M-n-v_2(h),
\]

which tends to infinity for fixed $h$.  Taking one more unit difference
multiplies by 9 and leaves the same valuation deficit, so the derivative
character cannot be constant on two surviving adjacent indices for all
large depths.  This is a nontermination result, not a cancellation result.

The algebra is not claimed as novel: the general geometric-phase identity
is already accepted by Lean in T13.  No new formal declaration was added.

## 4. Audit of the full-odd-coordinate selector

Put

\[
 D=2^{4M-r-4},\qquad Q=2^{3M-r},\qquad r=v_2(M+1).
\]

The quotient is $D/Q=2^{M-4}$, so $Q\mid D$ for every $M\ge4$.  Keeping
the actual $c_M/R_M$ fixed and varying an odd $w$ gives the starting seed

\[
 \frac{10^M}{16}\left(\frac wD+\frac{c_M}{R_M}\right)
 \equiv\frac{5^Mw}{Q}+\frac{10^Mc_M}{16R_M}\pmod1.
\]

Since $5^M$ is a unit modulo $Q$, odd $w$ runs through all odd grid
numerators.  Their spacing is $2/Q$, so their circle covering radius is
$1/Q$.  Any selected class modulo $Q$ has representatives in $[0,D)$; one
lies within distance $Q$ of the actual $w_M$, including the two endpoint
gaps.

For $P'=R_Mw'+Dc_M$, oddness of $w'$ makes $P'$ odd, while
$P'\equiv Dc_M\pmod {R_M}$ and $(c_M,R_M)=1$ prove
$(P',2R_M)=1$.  Thus the full denominator is not artificially inflated.
The rational displacement is

\[
 \left|\frac{P'}{16DR_M}-B_M\right|
 =\frac{|w'-w_M|}{16D}
 \le\frac Q{16D}=2^{-M}.
\]

If $n=M+t\le L_M$, multiplication of the initial $1/Q$ error gives

\[
 \frac{10^t}{Q}
 \le\frac{(8/5)^M}{2^{3M-r}}
 =\frac{2^r}{5^M}
 \le\frac{M+1}{5^M}.
\]

Because $1/9$ is fixed by times 10, every row term is within the stated
chord error of the common unit
$e(h(1/9-16B'_M))$.  The normalized mean therefore tends to that unit and
its magnitude tends to one.

The theorem fixes the actual **entire odd quotient modulo integers** and all
of its CRT coordinates.  It varies the dyadic coordinate and does not obey
the actual carry recurrence.  Accordingly it rules out uniform estimates
that discard the selected carry; it says nothing adverse about the actual
row.

## 5. Audit of the coarse-data separator

For $C=3^a$ minimal with $C\ge(M+1)^3$, one has
$C<3(M+1)^3$, $P^+(C)=3$, and $\log C=O(\log M)$.  If
$b=\lfloor\log_3(8M+5)\rfloor$, then
$3^b>(8M+5)/3>2M$; hence
$3^{4b}>(2M)^4\ge(M+1)^3$, proving $a\le4b$.

The integers coprime to 6 have cyclic gaps at most four.  Their points on
the $(DC)^{-1}$ grid therefore have covering radius $2/(DC)$.  CRT maps
such a numerator to an odd $w\bmod D$ and a unit
$\eta\bmod C$.  Combining any prescribed nonzero high-prime coordinates
with this $\eta$ reconstructs a numerator coprime to the entire odd modulus.

Finally, $A_n$ is divisible by 3, and

\[
 \frac{2A_{L_M}}{DC}
 <\frac{2^{r+1}}C
 \le\frac2{(M+1)^2}.
\]

The chord inequality gives the report's constant
$4\pi|h|/(M+1)^2$.  This construction varies both unresolved selectors and
is correctly labeled only as a separator for coarse row data.

## 6. Second exact checker

The companion
[`bbp_weighted_sum_differencing_self_audit_check.py`](bbp_weighted_sum_differencing_self_audit_check.py)
is independent of the primary checker and has SHA-256
`39665d0cc03870755e0a3b9f3ab84fb727d128c22bdcd9f51d35804f4b4bf512`.
It returned `PASS` after:

```text
coefficient and majorant checks: 513
row algebra checks: 592
inverse endpoint checks: 1426
iterated-difference checks: 2000
dyadic-boundary checks: 7968
full-odd-coordinate selector checks: 18881
coarse-coordinate separator checks: 9795
asserts_weighted_sum_bound: false
asserts_fourier_limit: false
asserts_fixed_return: false
asserts_v1: false
```

The selector tests use randomized odd moduli and quotients rather than the
primary checker's actual finite BBP rows.  All theorem-facing checks use
integer or rational arithmetic.  The two implementations therefore agree
without sharing code.

## Final boundary

The audited conclusion is negative but exact.  The parent's weighted sum is
the actual pi block up to an explicit $O_h(M^{-2})$ normalized error;
differencing only promotes frequency; and neither odd CRT data nor coarse
cofactor restrictions can be separated from the actual dyadic/cofactor
selectors.  The only live version of this route must exploit their joint
four-pole recurrence.  No such estimate, fixed return, or proof of V1 has
been obtained.
