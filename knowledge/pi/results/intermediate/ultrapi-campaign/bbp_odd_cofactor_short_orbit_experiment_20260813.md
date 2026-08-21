# BBP odd cofactor: square-root localization and an exact-kill no-go

Audit date: **2026-08-13 UTC**

Target: [problems/local/pi-digits.txt](../../problems/local/pi-digits.txt)

Target SHA-256:
`2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825`.

Provenance: Marcel's immutable local question has no external source URL;
none is invented here.

Parent report:
[bbp_actual_odd_quotient_attack.md](bbp_actual_odd_quotient_attack.md),
SHA-256
`d77e96b5bdce3bfd8278fa3b650d7a95d16bc86738c2af95a2d740919470c9fc`.

## Outcome and claim status

No fixed-sixteen return and no proof that every finite decimal word occurs in
pi was obtained. V1 remains a `conjecture`.

This branch makes two exact advances, both with status `proof sketch`.

1. The simple-pole localization from the parent report can be used for every
   **actually surviving** denominator prime
   (p>\sqrt{8M+5}), not only (p>M). After removing these explicit
   additive CRT coordinates, the remaining odd cofactor
   (C_M^{\square}) satisfies

   \[
       P^+(C_M^{\square})\leq\sqrt{8M+5},\qquad
       \log C_M^{\square}=O(\sqrt M\log M)=o(M).       \tag{1}
   \]

   The survival decision is the exact finite test
   (G_{M,p}\not\equiv0\pmod p), rather than a uniform height argument.
2. The tempting shortcut of choosing an exponent with
   (10^n\equiv16\pmod {C_M}) is rigorously impossible. Every cofactor in
   this report retains the full 5-primary denominator, and

   \[
       v_5(R_M)=\left\lfloor\log_5(8M+5)\right\rfloor. \tag{2}
   \]

   Hence (5\mid C_M), but (5\nmid10^n-16) for every (n\geq1).

The companion replay over (48\leq M\leq1000) has status `experiment`.
It uses exact rational and integer arithmetic. Finite evidence is not used as
a proof of an asymptotic return or non-return.

## 1. Explicit cofactor definitions

Retain the notation of the parent report:

\[
 B_M=\frac{P_M}{2^{K_M}R_M},\qquad
 K_M=4M-v_2(M+1),\qquad (P_M,2R_M)=1,               \tag{3}
\]

where (R_M) is odd, and put (X_M=8M+5). For an explicit cutoff
(Y\geq1), define

\[
 \begin{aligned}
 S_M(Y)&=\prod_{\substack{p\mid R_M,\ p>Y\\p^2>X_M}}p,\\
 C_M(Y)&=R_M/S_M(Y).                                \tag{4}
 \end{aligned}
\]

Every selected prime has exponent one. For (p>5), (p^2>X_M), the
parent report's localization gives a rational (G_{M,p}) such that

\[
 p\mid R_M\iff G_{M,p}\not\equiv0\pmod p,
 \qquad
 \gamma_{M,p}\equiv G_{M,p}\pmod p.               \tag{5}
\]

Thus (4) removes only actual, explicitly computable additive coordinates.
The replay uses four non-silent choices:

\[
 Y=M,\qquad Y=\lceil M/2\rceil,\qquad
 Y=\lceil M/4\rceil,\qquad Y=\lfloor\sqrt{X_M}\rfloor. \tag{6}
\]

The extra condition (p^2>X_M) remains in force for all four. The first
choice is exactly the cofactor behind (40cn)--(40co) of `ultrapi.md` once
(M\geq48). The fourth is denoted (C_M^{\square}).

### Square-root support reduction

For (C_M^{\square}), every prime divisor is at most
(\sqrt{X_M}). For (p>5), the pairwise-resultant argument in the parent
report gives

\[
     v_p(R_M)\leq\lfloor\log_pX_M\rfloor,            \tag{7}
\]

while the fixed primes 3 and 5 cost only (O(\log X_M)). Consequently

\[
 \begin{aligned}
 \log C_M^{\square}
 &\leq \vartheta(\sqrt{X_M})
   +\sum_{\ell\geq2}\vartheta(X_M^{1/\ell})
   +O(\log X_M)\\
 &=O(\sqrt{X_M}\log X_M)=o(M).                      \tag{8}
 \end{aligned}
\]

This proves (1) using only an elementary Chebyshev bound. It sharpens the
remaining prime-support bound from (O(M/\log M)) to (O(\sqrt M)), at the
price that the selected prime set is decided by the exact survival test (5)
rather than by a uniform numerator-height certificate. It does not estimate
the selected short orbit.

## 2. The exact 5-adic denominator

The BBP coefficient has the partial-fraction form

\[
 a(k)=\frac4{8k+1}-\frac2{8k+4}
      -\frac1{8k+5}-\frac1{8k+6}.                  \tag{9}
\]

Fix (M\geq0), write (X=8M+5), and put
(e=\lfloor\log_5X\rfloor\). The terms of 5-adic valuation (-e) among
(a(k)), (0\leq k\leq M), are completely explicit.

The first is

\[
 k_1=
 \begin{cases}
 (5^e-5)/8,&e\text{ odd},\\
 (5^e-1)/8,&e\text{ even}.
 \end{cases}                                       \tag{10}
\]

For odd (e), it comes from (8k_1+5=5^e) with leading residue
(-1\equiv4\pmod5). For even (e), it comes from
(8k_1+1=5^e) with leading residue (4\pmod5). There can be one further
term,

\[
                  k_2=(5^e-1)/2,                   \tag{11}
\]

if (k_2\leq M). It comes from (2k_2+1=5^e) in the second fraction of
(9), and its leading residue is (-1/2\equiv2\pmod5).

There are no others. Indeed, before (X) reaches (5^{e+1}), the only odd
multipliers of (5^e) available in (8k+1) or (8k+5) are (1) and
(3), and the multiplier (3) has neither required residue modulo 8. The
range of (2k+1) permits only multiplier 1, and
(4k+3\equiv3\pmod4) cannot equal (5^e\equiv1\pmod4).

Since (16^{-k}\equiv1\pmod5), the leading residue of

\[
                  B_M=\sum_{k=0}^{M}\frac{a(k)}{16^k}
\]

is either (4), when only (k_1) is present, or
(4+2\equiv1\pmod5), when both are present. It never cancels. Therefore

\[
 v_5(B_M)=-e,
 \qquad
 v_5(R_M)=e=\lfloor\log_5(8M+5)\rfloor,             \tag{12}
\]

which proves (2).

## 3. Exact annihilation is impossible

Let (C) be any cofactor in (4), and let its additive coordinate be
(eta/C). As in the parent report, ((\eta,C)=1), and, for integer exponents
(n\geq4),

\[
                  A_n=\frac{10^n-16}{16}.           \tag{13}
\]

For the depths considered here, none of the cutoffs removes 5, so (12)
gives (5\mid C). Exact annihilation of this coordinate would require

\[
 A_n\frac{\eta}{C}\in\mathbb Z
 \iff C\mid A_n
 \iff 10^n\equiv16\pmod C.                         \tag{14}
\]

But (10^n-16\equiv-1\pmod5) for every (n\geq1). Hence (14) has no
solution at any exponent, not merely none in the proportional BBP row.
Moreover,

\[
 v_5(10^n-16)=0,\qquad v_3(10^n-16)=1,              \tag{15}
\]

the second identity following from (10^n\equiv1\pmod9). If
(3^a5^b\mid C), then every gcd diagnostic necessarily misses the factor

\[
                         3^{\max(a-1,0)}5^b.         \tag{16}
\]

This is a no-go for the exact-kill shortcut, not for approximate
cancellation of the complete phase. CRT components can cancel as real
fractions, so (14) is sufficient but not necessary for a return.

There is also a useful exact reduction. Write (C=5^eC_0), and define the
additive CRT coordinates

\[
 \beta_5\equiv\eta C_0^{-1}\pmod{5^e},\qquad
 \beta_0\equiv\eta(5^e)^{-1}\pmod{C_0}.             \tag{17}
\]

For (n\geq\max(4,e)), (A_n\equiv-1\pmod{5^e}) and
(A_n\in\mathbb Z), so

\[
 A_n\frac{\eta}{C}
 \equiv-\frac{\beta_5}{5^e}
       +A_n\frac{\beta_0}{C_0}\pmod1.              \tag{18}
\]

The entire 5-primary component is a rowwise constant and may be moved into
the target offset. Only (C_0) remains as a moving power-orbit modulus.
This removes a polynomial factor, not the unresolved short-orbit problem.

## 4. Exact moderate-depth experiment

The replay constructs every (B_M) as a reduced `Fraction`, factors its
actual odd denominator, verifies every selected simple-pole coordinate, and
tests all

\[
         M\leq n\leq\lfloor\log_{10}(16^M)\rfloor  \tag{19}
\]

for (48\leq M\leq1000). It performs 398,862 coordinate checks and 409,640
short-orbit checks. All finite statements in this section are `experiment`.

The four cutoffs each produced zero exact congruences. This is also forced
by (12)--(14), so the absence itself is not statistical evidence.

After deleting the complete 3- and 5-primary parts, the checker separately
asks whether (16) lies in the subgroup generated by 10 at every remaining
prime power and whether the resulting discrete-log classes are compatible.
For each cutoff the result was:

- 948 of 953 rows have a local obstruction already at 11;
- the five rows (M=75,76,77,78,81) have local solutions but incompatible
  exponent classes (first exposed by the (13^2) condition);
- no row leaves a global exponent class, even before restricting to (19).

This subgroup calculation is finite `experiment`, not an asymptotic no-go.
Its identical outcome for all four cutoffs comes from the low prime-power
core, which those cutoffs do not alter.

Selected exact cofactor summaries are:

| (M) | (\log C_M(M)/M) | (\log C_M^{\square}/M) | (P^+(C_M^{\square})) | (v_5(C)) |
|---:|---:|---:|---:|---:|
| 48 | 1.238921 | 0.720741 | 19 | 3 |
| 100 | 1.111244 | 0.466191 | 23 | 4 |
| 200 | 1.131859 | 0.337218 | 37 | 4 |
| 500 | 1.076497 | 0.243661 | 61 | 5 |
| 1000 | 1.057121 | 0.180029 | 89 | 5 |

For the canonical (Y=M) cofactor, the largest observed value of

\[
             \frac{\log\gcd(C_M,10^n-16)}{\log C_M} \tag{20}
\]

over the full range was (0.189939), at ((M,n)=(61,68)); restricted to
(500\leq M\leq1000), it was (0.046434), at ((605,728)). For
(C_M^{\square}), the corresponding values were (0.236883), at
((50,50)), and (0.135890), at ((597,718)). These ratios neither prove
nor suggest an asymptotic bound without additional theory.

The smallest centered normalized residues

\[
 \min_n\frac{|[10^n-16]_{C,\mathrm{centered}}|}{C}   \tag{21}
\]

were (6.64\cdot10^{-5}) for (Y=M) and
(1.88\cdot10^{-4}) for the square-root cutoff. They are diagnostics for
the congruence shortcut only; they are not the complete phase in the parent
report.

## 5. Reproducible artifact

The standalone checker
[bbp_odd_cofactor_short_orbit_experiment_20260813_check.py](bbp_odd_cofactor_short_orbit_experiment_20260813_check.py)
has SHA-256
`5f35c22f15f65dc8ca979908dbf58e7c88879d022287ee480821f5f88fb4b664`.
It imports no branch checker. Run:

```text
python -m py_compile \
  work/ultrapi-resume/bbp_odd_cofactor_short_orbit_experiment_20260813_check.py
python \
  work/ultrapi-resume/bbp_odd_cofactor_short_orbit_experiment_20260813_check.py
```

The retained replay reports:

```text
claim_status=experiment
depth_range=48..1000
five_denominator_checks=1001
controlled_sqrt_coordinate_checks=398862
short_orbit_exact_checks=409640
exact_record_sha256=54a8fd54e294cee6df9025869858a85200bdc7007f2505a7c249372a099ea57c
each cutoff: exact_hits=0, local_obstruction=948,
             compatibility_obstruction=5, global_class=0
all exact checks passed
```

Passing `--show-exact` prints the exact cofactor, factorization, best gcd,
and centered residue for every row. The hash above commits to all 3,812 row
records in the default run.

## Sharp conclusion

The remaining odd uncertainty can be reduced more tightly than the
(p>M) cofactor: every actual simple-pole coordinate above
(\sqrt{8M+5}) is explicit, leaving (1). At the same time, exact modular
annihilation of that cofactor is permanently unavailable because its
5-primary coordinate survives with the exact valuation (12). Equation (18)
separates this frozen coordinate from the genuinely moving modulus.

What remains is still the selected, weighted (O(M))-term short-orbit
estimate for the full phase. Neither the square-root support reduction nor
the exact-kill no-go supplies that estimate. V1 therefore remains a
`conjecture`.
