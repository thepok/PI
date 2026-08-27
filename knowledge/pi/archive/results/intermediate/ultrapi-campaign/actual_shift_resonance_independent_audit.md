# Independent audit: actual shifted-grid resonance

Audit date: **2026-08-12 UTC**  
Target: [`problems/local/pi-digits.txt`](../../problems/local/pi-digits.txt)  
Target SHA-256: `2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825`  
Audited report:
[`actual_shift_resonance_attack.md`](actual_shift_resonance_attack.md)  
Audited report SHA-256:
`91ba678a89bc01a082024cb01050ff8ee1a50e6a848865ab266914c3499b4fca`  
Companion checker:
[`actual_shift_resonance_audit_check.py`](actual_shift_resonance_audit_check.py)  
Checker SHA-256:
`772d8f460cff9d272dfc104b3fe3d5c5a66e6e2df57c6923c018c7f2f76c0e9a`  
Primary report checker:
[`actual_shift_resonance_check.py`](actual_shift_resonance_check.py)  
Primary checker SHA-256:
`9933571acab5536921b646e02398d541877d5778817835fceaca92c4bf111ed4`

## Verdict and claim status

The report's central obstruction is sound. Its finite Fourier formula,
boundary-qualified Poisson formula, forbidden-word transfer product,
additive-CRT factorization, and reciprocity identity all have the displayed
normalizations and signs. In particular, the local prime characters really
recombine to

\[
                 e(\ell r_j/F_j)=e(\ell D_jx_j),
\]

so prime-by-prime denominator information has not produced a new averaging
variable. The nonzero term in equation (20) is an exact signed Fourier
reconstruction at the one actual Machin phase, not a sum over independent
prime choices.

This audit does **not** prove the canonical pi-digit conjecture. The
identities remain a `proof sketch`, because they are not in the verified Lean
track. The finite checker results below are an `experiment`. The dated source
applicability check is `literature-checked`. No estimate of the form (22),
unconditional cylinder hit, `candidate resolution`, or `verified resolution`
is present.

## 1. Finite Fourier identity and endpoint convention

For \(Q=FD\), write the sampled numerators as \(a=Fc+r\). Fourier inversion
with the report's convention is

\[
 g(a)=\frac1Q\sum_{h\bmod Q}G(h)e(ha/Q).
\]

Summing over \(0\le c<D\) gives

\[
 \sum_{c=0}^{D-1}e(hFc/Q)
 =\sum_{c=0}^{D-1}e(hc/D)
 =\begin{cases}D,&D\mid h,\\0,&D\nmid h.\end{cases}
\]

Writing \(h=Du\), \(0\le u<F\), leaves the factor \(D/Q=1/F\) and phase
\(e(ur/F)\). This is exactly equation (7), including its sign.

The floor convention is also correct at decimal endpoints. Since
\(0\le Fc+r<Q\),

\[
 g(Fc+r)=\mathbf1_{A_w(n)}
   \!\left(\left\lfloor M(c/D+r/(FD))\right\rfloor\right)
\]

is the indicator of the half-open cylinder containing the sample. Thus (7)
does not require a nonendpoint hypothesis.

For the Poisson version, direct integration over one cylinder gives

\[
 \int_{k/M}^{(k+1)/M}e(-hx)\,dx
 =e(-hk/M)\frac{1-e(-h/M)}{2\pi i h},
\]

which confirms equation (9). Summation over the \(D\)-grid leaves
\(h=\ell D\); its factor \(D\) cancels the \(D\) in the denominator
\(2\pi i\ell D\). This gives exactly the coefficient and phase in (10).
Because the survivor indicator has bounded variation, symmetric Dirichlet
partial sums converge to its point value away from discontinuities. The
report correctly imposes that condition for (10).

The endpoint exclusion is valid. Reducedness of \(b/(FD)\) implies
\((r,F)=1\). If

\[
       (Fc+r)/(FD)=k/M,
\]

then \(M(Fc+r)=kFD\), hence \(Mr\equiv0\pmod F\), and therefore
\(F\mid M=10^n\). Any prime divisor of \(F\) other than 2 or 5 makes this
impossible. This proves the stated sufficient endpoint exclusion; (7) covers
the remaining finite cases.

## 2. Forbidden-word transfer matrix

Let the padded decimal digits of \(k\) be \(a_1\ldots a_n\), most
significant first. Then

\[
 {k\over10^n}=\sum_{t=1}^n{a_t\over10^t},\qquad
 e(-hk/10^n)=\prod_{t=1}^ne(-ha_t/10^t).
\]

The prefix automaton accepts exactly the strings avoiding \(w\); deleting a
transition precisely when it completes \(w\) handles overlaps as well as
nonoverlaps. With the row convention
\((A_a)_{s,s'}=1\) for an allowed transition \(s\xrightarrow a s'\), the
product in equation (11) therefore sums the displayed phase over exactly
\(A_w(n)\). Its most-significant-to-least-significant order is correct.

The companion checker compares the transfer product as an exact coefficient
vector in \(\mathbb Z[z]/(z^{10^n}-1)\), not merely by floating-point
evaluation. It covered every one-digit and every two-digit forbidden word,
several depths, and five frequencies: 1,700 exact cases with no mismatch.

## 3. Additive CRT factorization and the localized units

The factorization in Section 4 requires the listed \(q\)'s to be pairwise
coprime complete primary components of \(F_j\). That is what the report's
decomposition \(F_j=F_{0,j}P_j\) supplies: the certified high primes occur
to denominator multiplicity one, and the remaining complete components are
placed in \(F_{0,j}\).

For such a component, equation (13) means

\[
       a_j\equiv(Q_j/q)u_{j,q}\pmod q.
\]

Since \(r_j\equiv a_j\pmod q\), \(Q_j/q=D_j(F_j/q)\), and
\(F_j/q\) is invertible modulo \(q\),

\[
 r_j(F_j/q)^{-1}\equiv D_ju_{j,q}\pmod q.
\]

The standard additive-CRT identity

\[
 e_{F_j}(\ell r_j)
 =\prod_{q\parallel F_j}
   e_q\!\left(\ell r_j(F_j/q)^{-1}\right)
\]

then gives equations (14) and (15) exactly. For a high prime \(p\),
\(u_{j,p}\equiv a_j(Q_j/p)^{-1}\) is precisely the reduction of the rational
\(p y_j=a_j/(Q_j/p)\) modulo \(p\). Substitution of the independently checked
general-band congruence

\[
 p y_j\equiv10^j\chi_4(p)C_s\pmod p
\]

gives (16). Here, as usual, the rational \(C_s\) is reduced in
\(\mathbb F_p\); the endpoint and coefficient exceptions ensure its
denominator is invertible and its localized unit is nonzero.

The existing exact band checker was rerun. It checked 10,098 complete seed
rows and 41 endpoint rows with zero mismatches; it also reproduced

\[
 C_3={38279241713339684\over12184551018734375},\qquad
 E_3={15305839961353732690848\over4871956171187883640625}.
\]

The companion audit checker separately tested the additive recombination in
1,350 exact integer/rational CRT cases. The product does not average over
\(p\): it is one additive character written in local coordinates. The
report's conclusion on this point is correct.

## 4. Reciprocity and the actual Machin phase

With \(b_j=F_jc_j+r_j\) and \(Q_j=F_jD_j\),

\[
 D_jx_j={b_j\over F_j}=c_j+{r_j\over F_j}.
\]

For every integer \(\ell\), the two exponents in (17) differ by the integer
\(\ell c_j\). Hence

\[
 e(\ell r_j/F_j)=e(\ell D_jx_j)
\]

with no approximation and no endpoint issue. The checker covered 6,750
exact rational instances, including positive and negative frequencies.

This identity is the decisive logical audit: equations (14) and (16) are a
CRT coordinate expansion of the already selected numerator phase. They do
not turn it into a family over which orthogonality can be invoked. Complete
period orthogonality in \(\ell\) is irrelevant unless the digital coefficient
is constant or otherwise controlled over that full period, which it is not.

## 5. Precise status of the signed sum

Away from endpoints, substituting the exact transfer product (11) and exact
CRT product (14) into (10) gives (20)--(21). Conjugate positive and negative
frequencies make \(\mathcal R_{j,w,n}\) real, although it is written as a
complex Fourier sum.

If the shadow-transfer hypotheses put the actual \(x_j\) in the avoidance
set, its quotient \(c_j\) is one of the sampled grid cells, so \(N\ge1\).
For a fixed nonempty forbidden word, its automaton entropy is strictly below
\(\log 10\); thus \(a_w(n)/10^n\) decays exponentially. Combining this with
\(D_j=\exp(o(j))\) and \(n=\Theta(j)\) gives the stated zero mode \(o(1)\).
Consequently the missing-word hypothesis forces

\[
 \mathcal R_{j,w,n}
 =N-{D_ja_w(n)\over10^n}\ge1-o(1).
\]

Conversely, (22) at one admissible shadow scale would imply \(N<1\). Since
\(N\) is a nonnegative integer, it would imply \(N=0\), contradicting the
shadowed missing-word point. Equation (22) is therefore a valid sufficient
new lemma.

No argument in the report proves (22). It is also not a consequence of the
local prime survival results: by (17), its phase is the actual Archimedean
Machin phase. Calling (20) the "first" missing sum is sound only in the
route-local sense that all preceding reductions have made it explicit; it
is not a novelty or priority claim and not a claim that every possible proof
of the pi-digit conjecture must pass through this sum.

## 6. Transfer diagonalization, cross-scale recurrence, and ASR

The added transfer-diagonalization section is also algebraically correct.
From the definition

\[
 B_t(h)=\sum_{a=0}^9 e(-ha/10^t)A_a,
\]

one has \(B_t(10^vh)=A\) for \(t\le v\), because its exponent is an integer,
and \(B_t(10^vh)=B_{t-v}(h)\) for \(t>v\). Preserving the product order gives
equation (23).

The proper-prefix automaton for a nonempty decimal word is primitive. Every
state is reachable from the empty state by reading the corresponding proper
prefix; from every state, appending a digit different from the first digit of
\(w\) returns to the empty state; and the empty state has such a self-loop.
Perron--Frobenius therefore gives a simple dominant eigenvalue
\(0<\lambda_w<10\), while Jordan decomposition gives the error form in (24)
for a suitable \(\lambda_{*,w}<\lambda_w\). For a one-digit forbidden word
the automaton is the scalar \(9\), so (25) follows exactly. The report is
right that a norm-only Perron estimate supplies no contraction on these
aliases. For a particular general-word suffix product, its Perron
coefficient could vanish; the report does not use (24) as a lower bound, so
this does not affect the obstruction.

For the phase comparison, \(x_j\equiv10^j\pi-s_j\pmod1\) immediately gives
(26). The elementary estimate \(|e(u)-e(v)|\le2\pi|u-v|\), the frequency
condition \(|q|D_j10^v\le10^n\), and \(0\le s_j<\rho^j\) give (27), including
its factor \(2\pi\). With \(\rho=10/625^3\),
\(100\rho=4.096\cdot10^{-6}\), so the displayed decay at
\(n\le2j+m-1\) is numerically correct.

T38's recurrence
\(x_{j+1}=\{10x_j+\Delta_j\}\) gives (28) after applying the integer
character \(e(\ell D_{j+1}\cdot)\). Writing its first factor as a frequency
on the previous \(D_j\)-lattice requires an integer
\(\ell'=10\ell D_{j+1}/D_j\), hence exactly the divisibility condition stated
in the report. In the absence of uniform denominator nesting, the recurrence
does not close the frequency family.

The actual-shift resonance statement (29) is a genuine `conjecture`, not a
result. If both bounds held, (21) would give \(0\le N\le3/4\), and integrality
would force \(N=0\); a valid missing-word shadow would simultaneously give
\(N\ge1\). The implication is correct. The first bound in (29) follows at the
`proof sketch` level from the growing-band conclusion
\(D_j=\exp(o(j))\) and forbidden-word entropy; that growing-band conclusion
is not itself a newly machine-checked theorem in this report. Bound (30)
would imply the second bound because \(D_j=\exp(o(j))\), but neither bound is
proved.

The primary checker for the new falsification experiment was inspected and
rerun. Its floor identity (31) is exact: if
\(z=10^{2j}r_j/F_j\), replacing \(z\) by \(\lfloor z\rfloor\) before division
by the integer \(D_j\) cannot cross the next integer boundary. The script
uses the reduced exact Machin seed, the complete 3-primary component as
\(D_j\), and exact integer/Fraction arithmetic. Its 8,580 prefix checks and
the two \(j=35\) witnesses reproduce the report's output exactly. This is an
`experiment`: it falsifies only the stated naive relative discrepancy bound,
not eventual ASR for the intended high-prime split.

## 7. Dated literature applicability check (`literature-checked`)

The four cited primary sources and their scopes were checked on
**2026-08-12 UTC**.

- Maynard's paper is explicitly a circle-method/Type I--II treatment of
  primes with one restricted digit. Its abstract and paper support the
  report's characterization of arithmetic averaging rather than a pointwise
  estimate at one Machin phase:
  [arXiv:1604.01041](https://arxiv.org/abs/1604.01041).
- Erdős--Mauduit--Sárközy's theorem is a quantitative residue-class result
  under coprimality conditions, with modulus below
  \(\exp(c\sqrt{\log N})\). It is not a zero-count result for a prescribed
  translated grid:
  [DOI 10.1006/jnth.1998.2229](https://doi.org/10.1006/jnth.1998.2229).
- Saavedra-Araya treats limiting distribution for each fixed modulus and
  includes forbidden-combination/sofic restrictions. The modulus is a fixed
  input to the Markov chain; this does not give the changing-modulus,
  depth-coupled estimate (22):
  [arXiv:2411.07418v2](https://arxiv.org/abs/2411.07418v2),
  [journal DOI](https://doi.org/10.1017/etds.2025.10256).
- Chow--Varj\'u--Yu prove polynomial bounds for bounded-height rational
  points in one-missing-digit Cantor sets using Fourier \(\ell^1\) dimension.
  Their theorem is not exclusion of a prescribed shifted grid point and has
  no Machin-phase input:
  [arXiv:2402.18395v2](https://arxiv.org/abs/2402.18395v2),
  [published DOI](https://doi.org/10.1016/j.aim.2026.110807).

The report properly describes this as a bounded dated search. Nothing in
these sources, as cited, supplies (22).

## 8. Defect list and qualifications

No substantive mathematical defect was found in equations (7), (10),
(11), (14)--(17), (20)--(23), or (25)--(32), subject to the hypotheses
stated in the report.

Three minor presentation findings were corrected in the audited report
without changing mathematical substance:

1. Equation (5) now uses the intended `\quad` spacing commands.
2. The text after (16) now explicitly says that rational \(C_{s(p)}\) is
   interpreted modulo \(p\), with invertibility supplied by the stated
   exceptions.
3. Section 8 now calls its bullets "alternative sufficient continuation
   routes," without asserting unproved literal equivalence among them.

No remaining notation or wording defect affecting the audit was found. The
obstruction itself is sound, and the report correctly avoids a solution
claim.

## 9. Reproducible checks (`experiment`)

Exact command:

```text
python3 work/ultrapi-resume/actual_shift_resonance_audit_check.py
```

Output:

```text
source_sha256=2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825
automaton_exact_cases=1700
grid_dft_cases=700 max_floating_dft_error=1.498e-13
endpoint_iff_exact_cases=200
crt_exact_cases=1350
reciprocity_exact_cases=6750
poisson_symmetric_H=20000 exact=4 value=3.999983311313 imag=0.000e+00 error=1.669e-05
```

The automaton, endpoint, CRT, and reciprocity counts are exact
integer/rational checks. The displayed DFT and symmetric-Dirichlet errors are
floating-point diagnostics only. Finite evidence is not a proof of the
identities or of the canonical conjecture.

The report's own exact falsification checker was rerun with its retained
range:

```text
python3 work/ultrapi-resume/actual_shift_resonance_check.py --max-j 80
```

It reproduced `exact_prefix_checks=8580`,
`naive_bound_abs_resonance_le_zero_mode_violations=65`, both \(j=35\)
witnesses, and `all exact checks passed` exactly as quoted in the report.

The underlying band checker was also rerun exactly:

```text
source_sha256=2bc65e79437f07eac1a31e7815b5ad738b1099884262880d42c6ded2b8f9a825
C3=38279241713339684/12184551018734375
E3=15305839961353732690848/4871956171187883640625
full_seed_rows=10098 endpoint_rows=41 predicted_nonsurvivors=152 mismatches=0
endpoint_scan_rows=2731 endpoint_bad=[(43, 41, 6, 13), (337, 131, 15, 31), (1352, 149, 54, 109), (1380, 137, 60, 121), (2157, 439, 29, 59), (2194, 479, 27, 55), (3513, 233, 90, 181)]
```

Bottom line: the report has isolated a genuine route-local obstruction. It
has not crossed it.
