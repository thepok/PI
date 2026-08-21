# Independent audit: BBP actual odd quotient and high-prime coordinates

Audit date: **2026-08-12 UTC**

Canonical target: [problems/local/pi-digits.txt](../../problems/local/pi-digits.txt),
SHA-256
2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825.
The immutable local question has no external source URL; none is invented.

Audited corrected artifacts:

- [bbp_actual_odd_quotient_attack.md](bbp_actual_odd_quotient_attack.md),
  SHA-256
  d77e96b5bdce3bfd8278fa3b650d7a95d16bc86738c2af95a2d740919470c9fc;
- [bbp_actual_odd_quotient_check.py](bbp_actual_odd_quotient_check.py),
  SHA-256
  c5f55d07feb84aa53285c8e0aee0bf32654a1bd7aed207ad518acfc07941d053.

Independent replay:

- [bbp_actual_odd_quotient_independent_check.py](bbp_actual_odd_quotient_independent_check.py),
  SHA-256
  f75a1624116d2f1ab5a3f66620648d5656b512ffc11d342a0caf9e8fd7e29786.

## Verdict

**PASS after two scoped mathematical corrections, one editorial
clarification, and one rigorous strengthening.**

The pre-audit report, SHA-256
907aa448c41538d064915e7b0b83f7efd65d46504740b97edeb93b7f3f1db2cb,
had a real domain mismatch in (27a)--(27b). It introduced the localization
only for \(p>M\), then used it down to \(p>M/L_M\). It also wrote an actual
CRT coordinate \(\gamma_{M,p}\) even when the raw denominator prime cancels;
the report's own finite data contain such rows. The corrected report now:

1. states the localization for the exact sufficient domain
   \(p>5,\ p^2>8M+5\), which includes the eventual moving cutoff;
2. states

   \[
    G_{M,p}\not\equiv0\pmod p
    \quad\Longleftrightarrow\quad v_p(R_M)=1,
   \]

   and defines the CRT coordinate only on that event;
3. recalls \(A_n=(10^n-16)/16\) where its lacunary identity is used; and
4. replaces the unnecessarily loose
   \(\log H=O(L\log L)\) by \(\log H=O(L)\). This permits
   \(L_M\asymp\log M\) and strengthens the cofactor support bound to
   \(P^+(C_M)=O(M/\log M)\).

The first two changes repair quantifier and definition defects, not the
underlying localization. The strengthened height argument proves
noncancellation on the asymptotic set used to form \(S_M\), so the cofactor
conclusion survives and becomes sharper.

The following claims rederive: the proportional-row equivalence (5), the
carry recurrence (15), the quotient recurrence (20), the full-pole formula
(27a), its block signs, the strengthened height cutoff, both PNT/AP mass
constants, the prime-power cofactor bound, the denominator asymptotic, the
CRT split (34), and the exact equivalence (41).

All infinite arithmetic and asymptotic conclusions have status "proof
sketch". The two deterministic replays have status "experiment". The primary
report's dated source-applicability record has status "literature-checked".
Nothing here proves a fixed-sixteen return. Canonical V1 remains a
"conjecture"; this branch is not a "candidate resolution".

## 1. Proportional window and floor choices

Let \(\lambda=\log_{10}16>1\) and

\[
 \Delta_M=\min_{M\le n\le\lfloor\lambda M\rfloor}
       \|(10^n-16)B_M\|_{\mathbb T}.
\]

If \(\liminf_M\Delta_M=0\), choose minimizing exponents along a vanishing
subsequence. They satisfy \(n_M\ge M\), so they tend to infinity, and the
uniform BBP transfer error tends to zero.

Conversely, for a return exponent \(n\), set
\(M=\lceil n/\lambda\rceil\). For all sufficiently large \(n\),
\(M\le n\); and \(n\le\lambda M\), hence the integrality of \(n\) gives
\(n\le\lfloor\lambda M\rfloor\). Thus the return lies in the proportional
row and transfers to \(B_M\). This proves (5), including its floor and
quantifier choices. The independent script checks these integer inequalities
without floating-point logarithms through its requested depth.

## 2. Complete dyadic carry and changing odd quotient

Write \(r_M=v_2(M+1)\),
\(s_M=4M-r_M-4\), \(D_M=2^{s_M}\), and

\[
 w_M\equiv2^{-r_M}F(M+1)\pmod {2^{s_M}},\qquad
 0\le w_M<2^{s_M}.
\]

Separating the first summand gives

\[
 F(X+1)=a(X)+16F(X).
\]

At the transition \(M\mapsto M+1\), the required precision before division
by \(2^{r_{M+1}}\) is exactly

\[
 s_{M+1}+r_{M+1}=4M,\qquad
 4M-(r_M+4)=s_M.
\]

Therefore the old \(w_M\) determines the second term modulo \(2^{4M}\), and
\(\alpha_M=[a(M+1)]_{2^{4M}}\) determines the first. The bracket is the
canonical residue of \(F(M+2)\). The previously audited isometry gives
\(v_2(F(M+2))=v_2(M+2)=r_{M+1}\), so division is legitimate and yields
exactly

\[
 w_{M+1}=2^{-r_{M+1}}
  [\,\alpha_M+2^{r_M+4}w_M\,]_{2^{4M}}.
\]

There is no lost carry bit and no use of a nested odd denominator.

Put \(y_M=w_M/D_M\),
\(c_M=(P_M-R_Mw_M)/D_M\), and \(q_M=c_M/R_M\). Since
\(P_M\equiv D_Mc_M\pmod {R_M}\) and both \(P_M,D_M\) are units modulo
\(R_M\), one has \((c_M,R_M)=1\). The exact identities

\[
 16B_M=y_M+q_M,\qquad
 16(B_{M+1}-B_M)={a(M+1)\over16^M}
\]

immediately give (20). Reducing its right side therefore has denominator
exactly \(R_{M+1}\); this is not an assumption about denominator nesting.

## 3. All-pole localization and survival

Let \(p>5\), \(p^2>8M+5\), and suppose a linear pole equals \(mp\). The
hypotheses imply \(m<p\), so every multiplier is a \(p\)-unit, and no pole
contains \(p^2\). At the four roots, direct substitution gives

\[
\begin{array}{c|c}
\text{pole}&p\,a(k)\\ \hline
2k+1=mp&-1/(2m)\\
4k+3=mp&-1/(2m)\\
8k+1=mp&4/m\\
8k+5=mp&-1/m.
\end{array}
\]

Reducing \(16^{1-k}\) by Fermat and Euler's criterion gives, respectively,

\[
 -{8\over m4^{m-1}},\qquad
 -{2^{6-m}\over m},\qquad
 {64(2/p)\over m2^{(m-1)/2}},\qquad
 -{64(2/p)\over m2^{(m-1)/2}}.
\]

Summing over the allowed positive odd multipliers is exactly (27a). All
other BBP summands are \(p\)-integral and disappear after multiplication by
\(p\). Consequently

\[
 16pB_M\equiv G_{M,p}\pmod p.                       \tag{A1}
\]

The raw common denominator has \(p\)-adic order at most one. Hence (A1)
proves the corrected survival equivalence. If the residue is nonzero, \(p\)
survives once and

\[
 c_M(R_M/p)^{-1}\equiv G_{M,p}\pmod p.
\]

If it is zero, \(p\) cancels and that CRT coordinate does not exist. This is
not hypothetical: both replays find the first genuine rows
\((9,19),(10,19),\ldots,(15,19),(19,13)\).

When \(p>M\), the multiplier lists truncate at \(1\), \(1,3\), and
\(1,3,5,7\) as stated. Direct summation gives exactly the eight rational
values in the report. Their numerators and denominators have no prime factor
above \(47\); therefore every possible \(p>M\) survives for \(M\ge48\).

## 4. Block order, sign, and strengthened height cutoff

For \(p\equiv1,5\pmod8\), block \(j\) appears as one positive term followed
by three negative terms:

\[
 {64\over(8j+1)16^j},\quad
 -{8\over(2j+1)16^j},\quad
 -{16\over(8j+5)16^j},\quad
 -{8\over(4j+3)16^j}.
\]

Its completed value is \(16a(j)/16^j>0\). Each earlier partial sum is the
positive completed value plus some still-unsubtracted negative magnitudes,
so every partial sum is positive.

For \(p\equiv3,7\pmod8\), the temporal order is three negative terms and
then the positive \(8/((8j+7)16^j)\). The completed value is

\[
 -{1\over16^j}\left(
 {8\over2j+1}+{32\over4j+1}+{32\over8j+3}
 -{8\over8j+7}\right)<0,
\]

because \(8/(2j+1)>8/(8j+7)\). The first three partial sums are negative
and the completed sum remains negative. The last event of block \(j\)
precedes the first event of block \(j+1\), so completed earlier blocks
cannot change the sign. Thus every nonempty rational \(G_{M,p}\) is nonzero
with sign determined by \(p\bmod4\).

For the strengthened height estimate, let
\(N=\lfloor(8M+5)/p\rfloor\). Every denominator in (27a) divides

\[
 D_N=2^{2N}\operatorname{lcm}(1,\ldots,N).
\]

This covers all four families and all partial blocks. Their total absolute
mass is uniformly bounded, since

\[
\begin{aligned}
 \sum_{\substack{m\ge1\\m\ {\rm odd}}}{8\over m4^{m-1}}
 &\le {128\over15},\\
 \sum_{\substack{m\ge1\\m\ {\rm odd}}}{2^{6-m}\over m}
 &\le {128\over3},\\
 2\sum_{\substack{m\ge1\\m\ {\rm odd}}}
       {64\over m2^{(m-1)/2}}
 &\le256.
\end{aligned}
\]

Thus \(|G_{M,p}|\le1536/5\), including every truncation. Chebyshev gives
\(\log D_N=O(N)\). In lowest terms, the denominator is at most \(D_N\) and
the numerator is at most \((1536/5)D_N\), proving
\(\log H(G_{M,p})=O(N)\).

If \(p>M/L\), then \(N\le8L+O(1)\), so
\(\log H(G_{M,p})\le C_0L\). Choose

\[
 L_M=\left\lfloor{\log M\over A}\right\rfloor,\qquad A>4C_0.
\]

For large \(M\), \(p>M/L_M\) implies \(p^2>8M+5\), and
\(H(G_{M,p})\le M^{1/4}<p\). Its nonzero rational numerator cannot vanish
modulo \(p\). Every possible prime above \(M/L_M\) therefore survives
exactly once. This yields

\[
 P^+(C_M)\le {M\over L_M}=O(M/\log M).
\]

## 5. Prime-support masses

The raw odd-prime support has this exact shape up to endpoint constants:

- every odd prime \(p\le4M+3\) occurs in at least one linear factor;
- above \(4M+3\), only \(p\equiv1,5\pmod8\) occur, up to \(8M+5\).

For the subset \(p>M\), the ordinary prime interval contributes
\(3M+o(M)\), while the two residue classes between \(4M\) and \(8M\)
contribute \(2M+o(M)\). Hence (27d) has constant \(5\).

For the full support, the first range contributes \(4M+o(M)\), and the two
classes above it again contribute \(2M+o(M)\). Hence (27h) has constant
\(6\). Removing primes at most \(M/L_M=O(M/\log M)\) costs \(o(M)\),
proving (27i). These uses require only the ordinary PNT and fixed-modulus
PNT/AP recorded in the primary report; they do not require a
uniform-in-modulus theorem.

## 6. Cofactor prime powers and denominator size

For \(p>5\), two of the four linear factors cannot both be divisible by
\(p\) at one index: their pairwise common divisors divide \(1,3,4,\) or
\(5\). Since every factor is at most \(X_M=8M+5\), the lcm of all raw term
denominators has

\[
 v_p\le\lfloor\log_pX_M\rfloor.
\]

Reduction can only lower this exponent. For \(p=3,5\), summing the four
individual bounds gives the stated factor \(4\).

After removing \(S_M\), every prime in \(C_M\) is at most
\(Y_M=M/L_M=O(M/\log M)\). Separating the squarefree layer from higher
powers gives

\[
\begin{aligned}
 \log C_M
 &\le\vartheta(Y_M)
   +\sum_{\ell\ge2}\vartheta(X_M^{1/\ell})+O(\log M)\\
 &=o(M).
\end{aligned}
\]

Chebyshev bounds the higher-power sum by
\(O(\sqrt M\log M)\), more than enough here. The lower bound
\(\log R_M\ge\log S_M=(6+o(1))M\) and the corresponding raw-support upper
bound, with this \(o(M)\) prime-power excess, prove

\[
 \log R_M=(6+o(1))M.
\]

No unproved cancellation assumption enters this deduction: survival above
the cutoff was established by the sign-height argument.

## 7. CRT split and exact remaining equivalence

Let \(R_M=S_MC_M\), with \((S_M,C_M)=1\). For each \(p\mid S_M\), let
\(\widehat\gamma_{M,p}\) be the least residue of the surviving coordinate,
and let \(\eta_M\equiv c_MS_M^{-1}\pmod {C_M}\). Multiplying

\[
 \sum_{p\mid S_M}{\widehat\gamma_{M,p}\over p}
       +{\eta_M\over C_M}
\]

by \(R_M\) proves congruence to \(c_M\) separately modulo every
\(p\mid S_M\) and modulo \(C_M\). The Chinese remainder theorem therefore
gives (34). Using rational \(G_{M,p}\) instead of its least modular residue
changes the displayed real representative but not the class modulo one.

Since \(A_n=(10^n-16)/16\) and
\(16B_M=y_M+c_M/R_M\), (34) gives (39) exactly modulo one. Therefore the
minimum \(\mathcal E_M\) in (40) equals \(\Delta_M\), not merely an upper
or lower bound. Section 1 gives

\[
 \liminf_M\mathcal E_M=0
 \quad\Longleftrightarrow\quad
 \liminf_n\|(10^n-16)\pi\|_{\mathbb T}=0.
\]

The separately audited Furstenberg/T69 bridge identifies the right side
with V1. It does not prove it. Thus (41) is an exact reduction and the
remaining weighted short-orbit estimate (43) is still the original hard
return problem in a more explicit coordinate system.

## 8. Independent replay

The independent checker imports no primary checker. It pins the source,
parent report, corrected primary report, and primary checker hashes. It
recomputes \(B_M\) with exact Fraction arithmetic and checks:

- exact integer floor/ceiling choices for (5);
- the functional and carry recurrences and the quotient recurrence;
- temporal order and sign of 64 complete multiplier blocks;
- 256 truncations against the uniform \(1536/5\) absolute-sum bound;
- raw support shape, every localization, the survival equivalence, and all
  eight high-prime constants;
- the common-denominator height majorant and every prime-power bound;
- a CRT decomposition using all surviving primes above \(\sqrt{8M+5}\);
- the phase factorization and equality of the two proportional minima.

The default depth 260 run passed. A separate depth 350 run retained:

    claim_status=experiment
    floor_choice_checks=417
    block_order_checks=64
    uniform_absolute_sum_checks=256
    carry_and_functional_checks=696
    quotient_recurrence_checks=348
    localization_checks=55768
    survival_equivalence_checks=55768
    eight_constant_checks=44847
    height_denominator_checks=55646
    exponent_bound_checks=59246
    support_shape_checks=76698
    crt_decomposition_checks=349
    phase_factorization_checks=12711
    proportional_phase_minimum_checks=346
    modular_cancellation_rows=122
    first_modular_cancellations=[(9, 19), (10, 19), (11, 19), (12, 19), (13, 19), (14, 19), (15, 19), (19, 13)]
    last_full_support_log_mass_over_M=5.830576054564
    last_p_gt_M_support_log_mass_over_M=4.908775458773
    all independent exact checks passed

The finite mass ratios are only an "experiment"; the constants \(6\) and
\(5\) come from the PNT/AP argument above. Likewise, no number of replayed
rows proves the asymptotic height cutoff or a return.

## Sharp conclusion

The corrected branch makes genuine inspectable progress: all odd prime
coordinates above \(M/L_M\) are explicit, their product has logarithmic mass
\((6+o(1))M\), and the remaining odd uncertainty lies on one cofactor with
\(\log C_M=o(M)\) and \(P^+(C_M)=O(M/\log M)\). The carry recurrence
supplies the complete dyadic coordinate.

What remains is not a denominator estimate. It is cancellation in the
selected, synchronized \(O(M)\)-term power orbit (42). Neither the
cofactor's subexponential size nor the explicit high-prime coordinates
implies that cancellation. No fixed-sixteen return is proved, so V1 remains
a "conjecture".
